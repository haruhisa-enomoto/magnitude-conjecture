import MagnitudeConjecture.Algebra.StringCohookDeletion

/-!
# Exhaustive endpoint operations for string words

Reading a word from left to right, either every letter is positive or there
is a last negative letter followed by a positive arm.  At a peak, the latter
factorization is exactly a maximal cohook which can be deleted.  Away from a
peak, admissibility extends a valid positive boundary arrow to a maximal hook.
Reversal gives the corresponding classification at the left endpoint.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- A word all of whose letters are positive, packaged as an extension of
the trivial word at its source. -/
def IsPurePositive (hR : IsAdmissible R) (C : Word R) : Prop :=
  Nonempty (PositiveExtension (vertex R hR C.source) C)

/-- A word all of whose letters are negative, expressed by reversing it to a
pure positive word. -/
def IsPureNegative (hR : IsAdmissible R) (C : Word R) : Prop :=
  IsPurePositive hR C.reverse

/-- A decomposition at the last negative letter of a word: an arbitrary
prefix, one negative letter, and a (possibly empty) positive tail. -/
structure CohookFactorization (C : Word R) where
  base : Word R
  vertex : Q
  arrow : vertex ⟶ base.target
  valid : IsString R (base.path.comp (negativeArrow arrow).toPath)
  tail : PositiveExtension (append R base (negativeArrow arrow) valid) C

namespace CohookFactorization

/-- If the final word is on a peak, its last-negative-letter factorization is
a maximal cohook reattachment and hence a cohook deletion. -/
def toCohookDeletion {C : Word R} (F : CohookFactorization C)
    (hpeak : C.StartsOnPeak) : CohookDeletion C F.base where
  cohook :=
    { vertex := F.vertex
      arrow := F.arrow
      valid := F.valid
      tail := F.tail
      maximal := hpeak }

end CohookFactorization

/-- Every certified path is obtained from the trivial word at its source by
an arbitrary right extension. -/
theorem rightExtensionFromVertex_nonempty_path
    (hR : IsAdmissible R) {x y : Q} (p : SignedPath x y) :
    ∀ h : IsString R p,
      Nonempty
        (RightExtension (vertex R hR x) (ofStringPath p h)) := by
  induction hlength : p.length using Nat.strong_induction_on
      generalizing x y with
  | h n ih =>
      cases p with
      | nil =>
          intro h
          have hword : ofStringPath Quiver.Path.nil h =
              vertex R hR x := by
            apply Word.ext
            · rfl
            · rfl
            · exact HEq.rfl
          exact ⟨Eq.mpr
            (congrArg (fun W : Word R ↦
              RightExtension (vertex R hR x) W) hword)
            RightExtension.base⟩
      | @cons middle _ p e =>
          intro hfull
          have hn : p.length + 1 = n := by
            simpa only [Quiver.Path.length_cons] using hlength
          have hpSub : IsContiguousSubpath p (p.cons e) := by
            refine ⟨Quiver.Path.nil, e.toPath, ?_⟩
            simp only [Quiver.Path.nil_comp,
              Quiver.Path.comp_toPath_eq_cons]
          have hp : IsString R p :=
            IsString.of_contiguousSubpath R hfull hpSub
          let prefixWord : Word R := ofStringPath p hp
          have happend : IsString R (prefixWord.path.comp e.toPath) := by
            simpa only [prefixWord, ofStringPath,
              Quiver.Path.comp_toPath_eq_cons] using hfull
          have hlt : p.length < n := by omega
          obtain ⟨extension⟩ := ih p.length hlt p rfl hp
          let next : RightExtension (vertex R hR x)
              (append R prefixWord e happend) :=
            RightExtension.step extension e happend
          have hword : append R prefixWord e happend =
              ofStringPath (p.cons e) hfull := by
            apply Word.ext
            · rfl
            · rfl
            · exact HEq.rfl
          exact ⟨Eq.mp
            (congrArg (fun W : Word R ↦
              RightExtension (vertex R hR x) W) hword)
            next⟩

/-- Every word is obtained from the trivial word at its source by an
arbitrary right extension. -/
theorem rightExtensionFromVertex_nonempty
    (hR : IsAdmissible R) (C : Word R) :
    Nonempty (RightExtension (vertex R hR C.source) C) := by
  have h := rightExtensionFromVertex_nonempty_path hR C.path C.isString
  simpa only [ofStringPath_word_path] using h

/-- An arbitrary right extension is either purely positive or its final
negative letter determines a negative-letter/positive-tail factorization of
the result. -/
theorem RightExtension.isPurePositive_or_cohookFactorization
    {C D : Word R} (extension : RightExtension C D) :
    Nonempty (PositiveExtension C D) ∨
      Nonempty (CohookFactorization D) := by
  induction extension with
  | base => exact Or.inl ⟨PositiveExtension.base⟩
  | @step E extension z e h ih =>
      cases e with
      | inl a =>
          rcases ih with hpositive | hfactor
          · obtain ⟨positive⟩ := hpositive
            exact Or.inl ⟨PositiveExtension.step positive a h⟩
          · obtain ⟨F⟩ := hfactor
            exact Or.inr ⟨
              { base := F.base
                vertex := F.vertex
                arrow := F.arrow
                valid := F.valid
                tail := PositiveExtension.step F.tail a h }⟩
      | inr a =>
          exact Or.inr ⟨
            { base := E
              vertex := z
              arrow := a
              valid := h
              tail := PositiveExtension.base }⟩

/-- Every word is either purely positive or has a last negative letter
followed by a positive tail. -/
theorem isPurePositive_or_cohookFactorization
    (hR : IsAdmissible R) (C : Word R) :
    IsPurePositive hR C ∨ Nonempty (CohookFactorization C) := by
  obtain ⟨extension⟩ := rightExtensionFromVertex_nonempty hR C
  exact extension.isPurePositive_or_cohookFactorization

/-- Exhaustive operation at the right endpoint: a word admits a maximal
hook, admits a maximal cohook deletion, or is purely positive. -/
theorem exists_hook_or_cohookDeletion_or_isPurePositive
    (hR : IsAdmissible R) (C : Word R) :
    (∃ D : Word R, Nonempty (HookExtension C D)) ∨
      (∃ D : Word R, Nonempty (CohookDeletion C D)) ∨
        IsPurePositive hR C := by
  classical
  by_cases hpeak : C.StartsOnPeak
  · rcases isPurePositive_or_cohookFactorization hR C with
      hpure | hfactor
    · exact Or.inr (Or.inr hpure)
    · obtain ⟨F⟩ := hfactor
      exact Or.inr (Or.inl ⟨F.base, ⟨F.toCohookDeletion hpeak⟩⟩)
  · left
    simp only [StartsOnPeak] at hpeak
    push Not at hpeak
    obtain ⟨z, a, hvalid⟩ := hpeak
    obtain ⟨D, hook, _⟩ :=
      HookExtension.exists_of_append_positive hR C a hvalid
    exact ⟨D, ⟨hook⟩⟩

/-- A right hook exists exactly when the word does not start on a peak. -/
theorem exists_hook_iff_not_startsOnPeak
    (hR : IsAdmissible R) (C : Word R) :
    (∃ D : Word R, Nonempty (HookExtension C D)) ↔
      ¬ C.StartsOnPeak := by
  constructor
  · rintro ⟨D, ⟨hook⟩⟩
    exact hook.not_startsOnPeak
  · intro hpeak
    simp only [StartsOnPeak] at hpeak
    push Not at hpeak
    obtain ⟨z, a, hvalid⟩ := hpeak
    obtain ⟨D, hook, _⟩ :=
      HookExtension.exists_of_append_positive hR C a hvalid
    exact ⟨D, ⟨hook⟩⟩

/-- A non-pure-positive word on a right peak has a maximal cohook which can
be deleted. -/
theorem exists_cohookDeletion_of_startsOnPeak_of_not_isPurePositive
    (hR : IsAdmissible R) (C : Word R)
    (hpeak : C.StartsOnPeak) (hpure : ¬ IsPurePositive hR C) :
    ∃ D : Word R, Nonempty (CohookDeletion C D) := by
  rcases isPurePositive_or_cohookFactorization hR C with
    hpure' | hfactor
  · exact False.elim (hpure hpure')
  · obtain ⟨F⟩ := hfactor
    exact ⟨F.base, ⟨F.toCohookDeletion hpeak⟩⟩

/-- Exhaustive operation at the left endpoint, obtained by reversal: a word
admits a maximal left hook, admits a maximal left cohook deletion, or is
purely negative. -/
theorem exists_leftHook_or_leftCohookDeletion_or_isPureNegative
    (hR : IsAdmissible R) (C : Word R) :
    Nonempty (LeftHookExtension C) ∨
      (∃ D : Word R, Nonempty (LeftCohookDeletion C D)) ∨
        IsPureNegative hR C := by
  rcases exists_hook_or_cohookDeletion_or_isPurePositive hR C.reverse with
    ⟨D, ⟨hook⟩⟩ | ⟨D, ⟨deletion⟩⟩ | hpure
  · exact Or.inl ⟨{ reverseResult := D, hook := hook }⟩
  · let reversedDeletion := deletion.toReverseLeftCohookDeletion
    have hsource : C.reverse.reverse = C := reverse_reverse R C
    let originalDeletion : LeftCohookDeletion C D.reverse :=
      Eq.mp
        (congrArg
          (fun W : Word R ↦ LeftCohookDeletion W D.reverse)
          hsource)
        reversedDeletion
    exact Or.inr (Or.inl ⟨D.reverse, ⟨originalDeletion⟩⟩)
  · exact Or.inr (Or.inr hpure)

/-- A left hook exists exactly when the word does not end on a peak. -/
theorem exists_leftHook_iff_not_endsOnPeak
    (hR : IsAdmissible R) (C : Word R) :
    Nonempty (LeftHookExtension C) ↔ ¬ C.EndsOnPeak := by
  constructor
  · rintro ⟨hook⟩
    exact hook.not_endsOnPeak
  · intro hpeak
    rw [EndsOnPeak] at hpeak
    obtain ⟨D, ⟨hook⟩⟩ :=
      (exists_hook_iff_not_startsOnPeak hR C.reverse).2 hpeak
    exact ⟨{ reverseResult := D, hook := hook }⟩

/-- A non-pure-negative word on a left peak has a maximal left cohook which
can be deleted. -/
theorem exists_leftCohookDeletion_of_endsOnPeak_of_not_isPureNegative
    (hR : IsAdmissible R) (C : Word R)
    (hpeak : C.EndsOnPeak) (hpure : ¬ IsPureNegative hR C) :
    ∃ D : Word R, Nonempty (LeftCohookDeletion C D) := by
  rcases exists_leftHook_or_leftCohookDeletion_or_isPureNegative hR C with
    hhook | hdeletion | hpure'
  · exact False.elim (hhook.elim fun hook ↦ hook.not_endsOnPeak hpeak)
  · exact hdeletion
  · exact False.elim (hpure hpure')

end StringWord.Word
end MagnitudeConjecture.BoundQuiver
