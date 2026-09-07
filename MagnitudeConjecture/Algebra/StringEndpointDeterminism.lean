import MagnitudeConjecture.Algebra.StringHookCohook
import MagnitudeConjecture.Algebra.StringPathCombinatorics

/-!
# Determinism after the first hook or cohook letter

The unsigned trivial word at a branching vertex may admit two extensions, so
global endpoint uniqueness is deliberately not asserted.  Once a first hook
or cohook letter has been chosen, however, reducedness excludes that same
displayed arrow from the opposite-sign tail.  The special-biserial degree-two
bound then makes the first tail arrow unique.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringWord.Word

/-- In a finite type of cardinality at most two, two elements different from
the same marked element coincide. -/
theorem eq_of_ne_of_ne_of_natCard_le_two
    {T : Type*} [Finite T] (a b c : T)
    (hba : b ≠ a) (hca : c ≠ a) (hcard : Nat.card T ≤ 2) :
    b = c := by
  classical
  by_contra hbc
  letI : Fintype T := Fintype.ofFinite T
  let f : Fin 3 → T := ![a, b, c]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hthree : 3 ≤ Fintype.card T := by
    simpa using Fintype.card_le_of_injective f hf
  have htwo : Fintype.card T ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  omega

variable {R : RelationFamily k Q}

/-- Positive displayed arrows which can be appended to a word while retaining
the string condition. -/
abbrev PositiveAppendArrow (C : Word R) :=
  {e : Quiver.Star C.target //
    IsString R (C.path.comp (positiveArrow e.2).toPath)}

/-- Negative displayed arrows which can be appended to a word while retaining
the string condition. -/
abbrev NegativeAppendArrow (C : Word R) :=
  {e : Quiver.Costar C.target //
    IsString R (C.path.comp (negativeArrow e.2).toPath)}

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
/-- A positive displayed arrow cannot be followed immediately by its formal
inverse in a string. -/
theorem positive_negative_not_string
    (C : Word R) {z : Q} (a : C.target ⟶ z)
    (h : IsString R
      ((C.path.comp (positiveArrow a).toPath).comp
        (negativeArrow a).toPath)) :
    False := by
  rcases h with ⟨hred, _, _⟩
  apply hred (positiveArrow a)
  refine ⟨C.path, Quiver.Path.nil, ?_⟩
  simp only [reverse_positiveArrow, Quiver.Path.comp_nil,
    Quiver.Path.comp_assoc]

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
/-- A negative displayed arrow cannot be followed immediately by its formal
inverse in a string. -/
theorem negative_positive_not_string
    (C : Word R) {z : Q} (a : z ⟶ C.target)
    (h : IsString R
      ((C.path.comp (negativeArrow a).toPath).comp
        (positiveArrow a).toPath)) :
    False := by
  rcases h with ⟨hred, _, _⟩
  apply hred (negativeArrow a)
  refine ⟨C.path, Quiver.Path.nil, ?_⟩
  simp only [reverse_negativeArrow, Quiver.Path.comp_nil,
    Quiver.Path.comp_assoc]

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
/-- After a chosen positive boundary arrow, reducedness excludes that arrow
from being the first negative-tail arrow. -/
theorem negativeTail_costar_ne_boundary
    (C : Word R) {z w : Q} (a : C.target ⟶ z) (b : w ⟶ z)
    (h : IsString R
      ((C.path.comp (positiveArrow a).toPath).comp
        (negativeArrow b).toPath)) :
    (⟨w, b⟩ : Quiver.Costar z) ≠ ⟨C.target, a⟩ := by
  intro hab
  cases hab
  exact positive_negative_not_string C a h

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
/-- After a chosen negative boundary arrow, reducedness excludes that arrow
from being the first positive-tail arrow. -/
theorem positiveTail_star_ne_boundary
    (C : Word R) {z w : Q} (a : z ⟶ C.target) (b : z ⟶ w)
    (h : IsString R
      ((C.path.comp (negativeArrow a).toPath).comp
        (positiveArrow b).toPath)) :
    (⟨w, b⟩ : Quiver.Star z) ≠ ⟨C.target, a⟩ := by
  intro hab
  cases hab
  exact negative_positive_not_string C a h

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
/-- Two consecutive negative letters in a string give a surviving ordinary
two-arrow path in the reversed word. -/
theorem consecutiveNegative_arrowMap_comp_ne_zero
    (C : Word R) {w x : Q} (b : w ⟶ C.target)
    (hb : IsString R (C.path.comp (negativeArrow b).toPath))
    (a : x ⟶ w)
    (ha : IsString R
      ((append R C (negativeArrow b) hb).path.comp
        (negativeArrow a).toPath)) :
    arrowMap R b ≫ arrowMap R a ≠ 0 := by
  change pathMap R b.toPath ≫ pathMap R a.toPath ≠ 0
  rw [pathMap_comp]
  apply ha.2.2 (a.toPath.comp b.toPath)
  refine ⟨Quiver.Path.nil, C.path.reverse, ?_⟩
  simp only [Quiver.Path.nil_comp, append_path]
  calc
    ((C.path.comp (negativeArrow b).toPath).comp
        (negativeArrow a).toPath).reverse =
        (negativeArrow a).toPath.reverse.comp
          (C.path.comp (negativeArrow b).toPath).reverse :=
      @Quiver.Path.reverse_comp (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) _ _ _ _
        (C.path.comp (negativeArrow b).toPath)
        (negativeArrow a).toPath
    _ = (positiveArrow a).toPath.comp
        ((positiveArrow b).toPath.comp C.path.reverse) := by
      rw [Quiver.Path.reverse_toPath, reverse_negativeArrow,
        @Quiver.Path.reverse_comp (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          C.path (negativeArrow b).toPath,
        Quiver.Path.reverse_toPath, Quiver.symmetrify_reverse]
      rfl
    _ = (positivePath (a.toPath.comp b.toPath)).comp C.path.reverse := by
      rw [positivePath_comp, positivePath_toPath (Q := Q),
        positivePath_toPath (Q := Q)]
      exact (Quiver.Path.comp_assoc _ _ _).symm

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
/-- Two consecutive positive letters in a string give a surviving ordinary
two-arrow path in the word itself. -/
theorem consecutivePositive_arrowMap_comp_ne_zero
    (C : Word R) {w x : Q} (b : C.target ⟶ w)
    (hb : IsString R (C.path.comp (positiveArrow b).toPath))
    (a : w ⟶ x)
    (ha : IsString R
      ((append R C (positiveArrow b) hb).path.comp
        (positiveArrow a).toPath)) :
    arrowMap R a ≫ arrowMap R b ≠ 0 := by
  change pathMap R a.toPath ≫ pathMap R b.toPath ≠ 0
  rw [pathMap_comp]
  apply ha.2.1 (b.toPath.comp a.toPath)
  refine ⟨C.path, Quiver.Path.nil, ?_⟩
  change (C.path.comp (positiveArrow b).toPath).comp
      (positiveArrow a).toPath =
    C.path.comp ((positivePath (b.toPath.comp a.toPath)).comp
      Quiver.Path.nil)
  rw [Quiver.Path.comp_nil, positivePath_comp,
    positivePath_toPath (Q := Q), positivePath_toPath (Q := Q)]
  exact Quiver.Path.comp_assoc _ _ _

/-- In a special-biserial presentation, the first negative-tail arrow after
a fixed positive hook boundary is unique. -/
theorem negativeTail_firstArrow_unique
    (P : SpecialBiserialPresentation k A Q)
    (C : Word P.toPresentation.relations) {z w₁ w₂ : Q}
    (a : C.target ⟶ z) (b₁ : w₁ ⟶ z) (b₂ : w₂ ⟶ z)
    (h₁ : IsString P.toPresentation.relations
      ((C.path.comp (positiveArrow a).toPath).comp
        (negativeArrow b₁).toPath))
    (h₂ : IsString P.toPresentation.relations
      ((C.path.comp (positiveArrow a).toPath).comp
        (negativeArrow b₂).toPath)) :
    (⟨w₁, b₁⟩ : Quiver.Costar z) = ⟨w₂, b₂⟩ := by
  apply eq_of_ne_of_ne_of_natCard_le_two
    (⟨C.target, a⟩ : Quiver.Costar z)
  · exact negativeTail_costar_ne_boundary C a b₁ h₁
  · exact negativeTail_costar_ne_boundary C a b₂ h₂
  · exact P.arrows_ending_le_two z

/-- In a special-biserial presentation, the first positive-tail arrow after
a fixed negative cohook boundary is unique. -/
theorem positiveTail_firstArrow_unique
    (P : SpecialBiserialPresentation k A Q)
    (C : Word P.toPresentation.relations) {z w₁ w₂ : Q}
    (a : z ⟶ C.target) (b₁ : z ⟶ w₁) (b₂ : z ⟶ w₂)
    (h₁ : IsString P.toPresentation.relations
      ((C.path.comp (negativeArrow a).toPath).comp
        (positiveArrow b₁).toPath))
    (h₂ : IsString P.toPresentation.relations
      ((C.path.comp (negativeArrow a).toPath).comp
        (positiveArrow b₂).toPath)) :
    (⟨w₁, b₁⟩ : Quiver.Star z) = ⟨w₂, b₂⟩ := by
  apply eq_of_ne_of_ne_of_natCard_le_two
    (⟨C.target, a⟩ : Quiver.Star z)
  · exact positiveTail_star_ne_boundary C a b₁ h₁
  · exact positiveTail_star_ne_boundary C a b₂ h₂
  · exact P.arrows_starting_le_two z

/-- Once the positive boundary arrow is fixed, a negative tail is uniquely
determined by its number of steps.  The endpoint word and the arm witness are
both retained in the dependent pair. -/
theorem negativeTail_eq_of_steps_eq
    (P : SpecialBiserialPresentation k A Q)
    (C : Word P.toPresentation.relations) {z : Q}
    (a : C.target ⟶ z)
    (ha : IsString P.toPresentation.relations
      (C.path.comp (positiveArrow a).toPath))
    {D₁ D₂ : Word P.toPresentation.relations}
    (tail₁ : NegativeExtension
      (append P.toPresentation.relations C (positiveArrow a) ha) D₁)
    (tail₂ : NegativeExtension
      (append P.toPresentation.relations C (positiveArrow a) ha) D₂)
    (hsteps : tail₁.steps = tail₂.steps) :
    (⟨D₁, tail₁⟩ : Σ D, NegativeExtension
        (append P.toPresentation.relations C (positiveArrow a) ha) D) =
      ⟨D₂, tail₂⟩ := by
  induction tail₁ generalizing D₂ with
  | base =>
      cases tail₂ with
      | base => rfl
      | step arm b hb => simp [NegativeExtension.steps] at hsteps
  | @step E tail₁ x b₁ hb₁ ih =>
      cases tail₂ with
      | base => simp [NegativeExtension.steps] at hsteps
      | @step F tail₂ y b₂ hb₂ =>
          have hinner : tail₁.steps = tail₂.steps := by
            simpa [NegativeExtension.steps] using hsteps
          have hpairs := ih tail₂ hinner
          cases hpairs
          cases tail₁ with
          | base =>
              have hbb : (⟨x, b₁⟩ : Quiver.Costar z) = ⟨y, b₂⟩ :=
                negativeTail_firstArrow_unique P C a b₁ b₂ hb₁ hb₂
              cases hbb
              rfl
          | @step E₀ inner w b hb =>
              have hb₁zero :
                  arrowMap P.toPresentation.relations b ≫
                    arrowMap P.toPresentation.relations b₁ ≠ 0 :=
                consecutiveNegative_arrowMap_comp_ne_zero E₀ b hb b₁ hb₁
              have hb₂zero :
                  arrowMap P.toPresentation.relations b ≫
                    arrowMap P.toPresentation.relations b₂ ≠ 0 :=
                consecutiveNegative_arrowMap_comp_ne_zero E₀ b hb b₂ hb₂
              have hbb : (⟨x, b₁⟩ : Quiver.Costar w) = ⟨y, b₂⟩ := by
                exact congrArg Subtype.val
                  (@Subsingleton.elim _
                    (P.leftContinuationArrow_subsingleton b)
                    (⟨⟨x, b₁⟩, hb₁zero⟩ : P.LeftContinuationArrow b)
                    (⟨⟨y, b₂⟩, hb₂zero⟩ : P.LeftContinuationArrow b))
              cases hbb
              rfl

/-- Once the negative boundary arrow is fixed, a positive tail is uniquely
determined by its number of steps. -/
theorem positiveTail_eq_of_steps_eq
    (P : SpecialBiserialPresentation k A Q)
    (C : Word P.toPresentation.relations) {z : Q}
    (a : z ⟶ C.target)
    (ha : IsString P.toPresentation.relations
      (C.path.comp (negativeArrow a).toPath))
    {D₁ D₂ : Word P.toPresentation.relations}
    (tail₁ : PositiveExtension
      (append P.toPresentation.relations C (negativeArrow a) ha) D₁)
    (tail₂ : PositiveExtension
      (append P.toPresentation.relations C (negativeArrow a) ha) D₂)
    (hsteps : tail₁.steps = tail₂.steps) :
    (⟨D₁, tail₁⟩ : Σ D, PositiveExtension
        (append P.toPresentation.relations C (negativeArrow a) ha) D) =
      ⟨D₂, tail₂⟩ := by
  induction tail₁ generalizing D₂ with
  | base =>
      cases tail₂ with
      | base => rfl
      | step arm b hb => simp [PositiveExtension.steps] at hsteps
  | @step E tail₁ x b₁ hb₁ ih =>
      cases tail₂ with
      | base => simp [PositiveExtension.steps] at hsteps
      | @step F tail₂ y b₂ hb₂ =>
          have hinner : tail₁.steps = tail₂.steps := by
            simpa [PositiveExtension.steps] using hsteps
          have hpairs := ih tail₂ hinner
          cases hpairs
          cases tail₁ with
          | base =>
              have hbb : (⟨x, b₁⟩ : Quiver.Star z) = ⟨y, b₂⟩ :=
                positiveTail_firstArrow_unique P C a b₁ b₂ hb₁ hb₂
              cases hbb
              rfl
          | @step E₀ inner w b hb =>
              have hb₁zero :
                  arrowMap P.toPresentation.relations b₁ ≫
                    arrowMap P.toPresentation.relations b ≠ 0 :=
                consecutivePositive_arrowMap_comp_ne_zero E₀ b hb b₁ hb₁
              have hb₂zero :
                  arrowMap P.toPresentation.relations b₂ ≫
                    arrowMap P.toPresentation.relations b ≠ 0 :=
                consecutivePositive_arrowMap_comp_ne_zero E₀ b hb b₂ hb₂
              have hbb : (⟨x, b₁⟩ : Quiver.Star w) = ⟨y, b₂⟩ := by
                exact congrArg Subtype.val
                  (@Subsingleton.elim _
                    (P.rightContinuationArrow_subsingleton b)
                    (⟨⟨x, b₁⟩, hb₁zero⟩ : P.RightContinuationArrow b)
                    (⟨⟨y, b₂⟩, hb₂zero⟩ : P.RightContinuationArrow b))
              cases hbb
              rfl

/-- Two maximal negative tails after the same positive boundary are equal,
including their endpoint words and arm witnesses. -/
theorem negativeTail_eq_of_maximal
    (P : SpecialBiserialPresentation k A Q)
    (C : Word P.toPresentation.relations) {z : Q}
    (a : C.target ⟶ z)
    (ha : IsString P.toPresentation.relations
      (C.path.comp (positiveArrow a).toPath))
    {D₁ D₂ : Word P.toPresentation.relations}
    (tail₁ : NegativeExtension
      (append P.toPresentation.relations C (positiveArrow a) ha) D₁)
    (tail₂ : NegativeExtension
      (append P.toPresentation.relations C (positiveArrow a) ha) D₂)
    (hmax₁ : D₁.StartsInDeep) (hmax₂ : D₂.StartsInDeep) :
    (⟨D₁, tail₁⟩ : Σ D, NegativeExtension
        (append P.toPresentation.relations C (positiveArrow a) ha) D) =
      ⟨D₂, tail₂⟩ := by
  apply negativeTail_eq_of_steps_eq P C a ha tail₁ tail₂
  apply Nat.le_antisymm
  · by_contra hle
    have hlt : tail₂.steps < tail₁.steps := Nat.lt_of_not_ge hle
    rcases tail₁.exists_prefix_of_steps_le
        (n := tail₂.steps + 1) (by omega) with
      ⟨E, initial, hinitial, suffix, hsuffix⟩
    cases initial with
    | base => simp [NegativeExtension.steps] at hinitial
    | @step F inner w b hb =>
        have hinner : tail₂.steps = inner.steps := by
          simp only [NegativeExtension.steps] at hinitial
          omega
        have hpairs := negativeTail_eq_of_steps_eq P C a ha
          tail₂ inner hinner
        cases hpairs
        exact hmax₂ b hb
  · by_contra hle
    have hlt : tail₁.steps < tail₂.steps := Nat.lt_of_not_ge hle
    rcases tail₂.exists_prefix_of_steps_le
        (n := tail₁.steps + 1) (by omega) with
      ⟨E, initial, hinitial, suffix, hsuffix⟩
    cases initial with
    | base => simp [NegativeExtension.steps] at hinitial
    | @step F inner w b hb =>
        have hinner : tail₁.steps = inner.steps := by
          simp only [NegativeExtension.steps] at hinitial
          omega
        have hpairs := negativeTail_eq_of_steps_eq P C a ha
          tail₁ inner hinner
        cases hpairs
        exact hmax₁ b hb

/-- Two maximal positive tails after the same negative boundary are equal. -/
theorem positiveTail_eq_of_maximal
    (P : SpecialBiserialPresentation k A Q)
    (C : Word P.toPresentation.relations) {z : Q}
    (a : z ⟶ C.target)
    (ha : IsString P.toPresentation.relations
      (C.path.comp (negativeArrow a).toPath))
    {D₁ D₂ : Word P.toPresentation.relations}
    (tail₁ : PositiveExtension
      (append P.toPresentation.relations C (negativeArrow a) ha) D₁)
    (tail₂ : PositiveExtension
      (append P.toPresentation.relations C (negativeArrow a) ha) D₂)
    (hmax₁ : D₁.StartsOnPeak) (hmax₂ : D₂.StartsOnPeak) :
    (⟨D₁, tail₁⟩ : Σ D, PositiveExtension
        (append P.toPresentation.relations C (negativeArrow a) ha) D) =
      ⟨D₂, tail₂⟩ := by
  apply positiveTail_eq_of_steps_eq P C a ha tail₁ tail₂
  apply Nat.le_antisymm
  · by_contra hle
    have hlt : tail₂.steps < tail₁.steps := Nat.lt_of_not_ge hle
    rcases tail₁.exists_prefix_of_steps_le
        (n := tail₂.steps + 1) (by omega) with
      ⟨E, initial, hinitial, suffix, hsuffix⟩
    cases initial with
    | base => simp [PositiveExtension.steps] at hinitial
    | @step F inner w b hb =>
        have hinner : tail₂.steps = inner.steps := by
          simp only [PositiveExtension.steps] at hinitial
          omega
        have hpairs := positiveTail_eq_of_steps_eq P C a ha
          tail₂ inner hinner
        cases hpairs
        exact hmax₂ b hb
  · by_contra hle
    have hlt : tail₁.steps < tail₂.steps := Nat.lt_of_not_ge hle
    rcases tail₂.exists_prefix_of_steps_le
        (n := tail₁.steps + 1) (by omega) with
      ⟨E, initial, hinitial, suffix, hsuffix⟩
    cases initial with
    | base => simp [PositiveExtension.steps] at hinitial
    | @step F inner w b hb =>
        have hinner : tail₁.steps = inner.steps := by
          simp only [PositiveExtension.steps] at hinitial
          omega
        have hpairs := positiveTail_eq_of_steps_eq P C a ha
          tail₁ inner hinner
        cases hpairs
        exact hmax₁ b hb

namespace HookExtension

/-- Forget a maximal hook down to its chosen valid positive boundary arrow. -/
def boundary {C : Word R} :
    (Σ D, HookExtension C D) → C.PositiveAppendArrow
  | ⟨_, hook⟩ => ⟨⟨hook.vertex, hook.arrow⟩, hook.valid⟩

/-- In a special-biserial presentation, two maximal hooks with the same
chosen positive boundary arrow are the same dependent hook extension. -/
theorem eq_of_boundary_eq
    (P : SpecialBiserialPresentation k A Q)
    {C D₁ D₂ : Word P.toPresentation.relations}
    (hook₁ : HookExtension C D₁) (hook₂ : HookExtension C D₂)
    (hboundary : (⟨hook₁.vertex, hook₁.arrow⟩ : Quiver.Star C.target) =
      ⟨hook₂.vertex, hook₂.arrow⟩) :
    (⟨D₁, hook₁⟩ : Σ D, HookExtension C D) = ⟨D₂, hook₂⟩ := by
  rcases hook₁ with ⟨z₁, a₁, ha₁, tail₁, hmax₁⟩
  rcases hook₂ with ⟨z₂, a₂, ha₂, tail₂, hmax₂⟩
  dsimp only at hboundary
  cases hboundary
  have hvalid : ha₁ = ha₂ := Subsingleton.elim _ _
  cases hvalid
  have htail := negativeTail_eq_of_maximal P C a₁ ha₁
    tail₁ tail₂ hmax₁ hmax₂
  cases htail
  rfl

/-- Maximal hooks over a fixed word are in bijection with the valid positive
boundary arrows.  Multiple boundaries at an unsigned trivial word remain
distinct. -/
def boundaryEquiv
    (P : SpecialBiserialPresentation k A Q)
    (C : Word P.toPresentation.relations) :
    (Σ D, HookExtension C D) ≃ C.PositiveAppendArrow :=
  Equiv.ofBijective boundary ⟨by
    intro hook₁ hook₂ h
    exact eq_of_boundary_eq P hook₁.2 hook₂.2
      (congrArg Subtype.val h), by
    rintro ⟨⟨z, a⟩, ha⟩
    rcases exists_of_append_positive P.toPresentation.admissible C a ha with
      ⟨D, hook, hboundary⟩
    refine ⟨⟨D, hook⟩, ?_⟩
    apply Subtype.ext
    exact hboundary⟩

end HookExtension

namespace CohookExtension

/-- Forget a maximal cohook down to its chosen valid negative boundary
arrow. -/
def boundary {C : Word R} :
    (Σ D, CohookExtension C D) → C.NegativeAppendArrow
  | ⟨_, cohook⟩ => ⟨⟨cohook.vertex, cohook.arrow⟩, cohook.valid⟩

/-- In a special-biserial presentation, two maximal cohooks with the same
chosen negative boundary arrow are the same dependent cohook extension. -/
theorem eq_of_boundary_eq
    (P : SpecialBiserialPresentation k A Q)
    {C D₁ D₂ : Word P.toPresentation.relations}
    (cohook₁ : CohookExtension C D₁)
    (cohook₂ : CohookExtension C D₂)
    (hboundary :
      (⟨cohook₁.vertex, cohook₁.arrow⟩ : Quiver.Costar C.target) =
        ⟨cohook₂.vertex, cohook₂.arrow⟩) :
    (⟨D₁, cohook₁⟩ : Σ D, CohookExtension C D) =
      ⟨D₂, cohook₂⟩ := by
  rcases cohook₁ with ⟨z₁, a₁, ha₁, tail₁, hmax₁⟩
  rcases cohook₂ with ⟨z₂, a₂, ha₂, tail₂, hmax₂⟩
  dsimp only at hboundary
  cases hboundary
  have hvalid : ha₁ = ha₂ := Subsingleton.elim _ _
  cases hvalid
  have htail := positiveTail_eq_of_maximal P C a₁ ha₁
    tail₁ tail₂ hmax₁ hmax₂
  cases htail
  rfl

/-- Maximal cohooks over a fixed word are in bijection with the valid negative
boundary arrows. -/
def boundaryEquiv
    (P : SpecialBiserialPresentation k A Q)
    (C : Word P.toPresentation.relations) :
    (Σ D, CohookExtension C D) ≃ C.NegativeAppendArrow :=
  Equiv.ofBijective boundary ⟨by
    intro cohook₁ cohook₂ h
    exact eq_of_boundary_eq P cohook₁.2 cohook₂.2
      (congrArg Subtype.val h), by
    rintro ⟨⟨z, a⟩, ha⟩
    rcases exists_of_append_negative P.toPresentation.admissible C a ha with
      ⟨D, cohook, hboundary⟩
    refine ⟨⟨D, cohook⟩, ?_⟩
    apply Subtype.ext
    exact hboundary⟩

end CohookExtension

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
