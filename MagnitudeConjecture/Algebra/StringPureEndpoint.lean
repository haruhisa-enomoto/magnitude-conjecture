import MagnitudeConjecture.Algebra.StringEndpointClassification

/-!
# Pure-sign exceptional string endpoints

The exhaustive endpoint classification leaves a pure-positive alternative
on the right and a pure-negative alternative on the left.  This file makes
those alternatives literal at the level of signed-path signs, proves that
they overlap only for a vertex word, and packages the endpoint alternatives
so that a pure case is reached only at a peak.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord

/-- Reversing a signed path reverses the sign list and complements every
sign.  Recall that `signedPathSigns` lists letters from the end backwards. -/
@[simp]
theorem signedPathSigns_reverse {x y : Quiver.Symmetrify Q}
    (p : Quiver.Path x y) :
    signedPathSigns p.reverse =
      (signedPathSigns p).reverse.map (!·) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      cases e <;>
        simp [signedPathSigns, ih, Quiver.symmetrify_reverse] <;> rfl

namespace Word

variable {R : RelationFamily k Q}

/-- A positive arm prepends one `false` sign for every appended letter. -/
theorem PositiveExtension.signedPathSigns_eq
    {C D : Word R} (arm : PositiveExtension C D) :
    signedPathSigns D.path =
      List.replicate arm.steps false ++ signedPathSigns C.path := by
  induction arm with
  | base => rfl
  | step arm a h ih =>
      simp only [append_path, PositiveExtension.steps]
      rw [Quiver.Path.comp_toPath_eq_cons]
      simp only [signedPathSigns, positiveArrow]
      calc
        false :: signedPathSigns _ = false ::
            (List.replicate arm.steps false ++ signedPathSigns C.path) :=
          congrArg (List.cons false) ih
        _ = List.replicate (arm.steps + 1) false ++
            signedPathSigns C.path := by
          simp only [List.replicate_succ, List.cons_append]

/-- A length-zero signed path is heterogeneously equal to the trivial path
at its source. -/
private theorem signedPath_heq_nil_of_length_eq_zero
    {x y : Q} (p : SignedPath x y) (hlength : p.length = 0) :
    HEq p (Quiver.Path.nil : SignedPath x x) := by
  cases p with
  | nil => exact HEq.rfl
  | cons p e => simp at hlength

/-- A pure-positive word has only positive signed letters. -/
theorem IsPurePositive.signedPathSigns_eq
    (hR : IsAdmissible R) {C : Word R}
    (hpure : C.IsPurePositive hR) :
    signedPathSigns C.path = List.replicate C.length false := by
  obtain ⟨arm⟩ := hpure
  rw [arm.signedPathSigns_eq]
  simp only [vertex, signedPathSigns]
  have hlength := arm.result_length
  simp only [vertex_length, zero_add] at hlength
  rw [hlength]
  exact List.append_nil _

/-- A pure-negative word has only negative signed letters. -/
theorem IsPureNegative.signedPathSigns_eq
    (hR : IsAdmissible R) {C : Word R}
    (hpure : C.IsPureNegative hR) :
    signedPathSigns C.path = List.replicate C.length true := by
  have hreverse :=
    IsPurePositive.signedPathSigns_eq hR hpure
  calc
    signedPathSigns C.path = signedPathSigns C.reverse.path.reverse := by
      change signedPathSigns C.path =
        signedPathSigns C.path.reverse.reverse
      exact congrArg signedPathSigns
        (Quiver.Path.reverse_reverse C.path).symm
    _ = (signedPathSigns C.reverse.path).reverse.map (!·) :=
      signedPathSigns_reverse C.reverse.path
    _ = (List.replicate C.reverse.length false).reverse.map (!·) := by
      rw [hreverse]
    _ = List.replicate C.length true := by simp

/-- Every length-zero word is the trivial word at its source and hence is
purely positive. -/
theorem isPurePositive_of_length_eq_zero
    (hR : IsAdmissible R) (C : Word R) (hlength : C.length = 0) :
    C.IsPurePositive hR := by
  have hsourceTarget : C.source = C.target :=
    C.path.eq_of_length_zero hlength
  have hword : C = vertex R hR C.source := by
    apply Word.ext
    · rfl
    · exact hsourceTarget.symm
    · exact signedPath_heq_nil_of_length_eq_zero C.path hlength
  rw [hword]
  exact ⟨PositiveExtension.base⟩

/-- A word is simultaneously pure-positive and pure-negative exactly when
it is a vertex word. -/
theorem isPurePositive_and_isPureNegative_iff_length_eq_zero
    (hR : IsAdmissible R) (C : Word R) :
    C.IsPurePositive hR ∧ C.IsPureNegative hR ↔ C.length = 0 := by
  constructor
  · rintro ⟨hpositive, hnegative⟩
    have hfalse := hpositive.signedPathSigns_eq hR
    have htrue := hnegative.signedPathSigns_eq hR
    have heq : List.replicate C.length false =
        List.replicate C.length true := hfalse.symm.trans htrue
    cases hlength : C.length with
    | zero => rfl
    | succ n =>
        rw [hlength] at heq
        simp at heq
  · intro hlength
    refine ⟨isPurePositive_of_length_eq_zero hR C hlength, ?_⟩
    exact isPurePositive_of_length_eq_zero hR C.reverse (by
      simpa only [reverse_length] using hlength)

/-- A nontrivial pure-positive word cannot also be pure-negative. -/
theorem IsPurePositive.not_isPureNegative_of_length_pos
    (hR : IsAdmissible R) {C : Word R}
    (hpositive : C.IsPurePositive hR) (hlength : 0 < C.length) :
    ¬ C.IsPureNegative hR := by
  intro hnegative
  have hzero :=
    (isPurePositive_and_isPureNegative_iff_length_eq_zero hR C).1
      ⟨hpositive, hnegative⟩
  omega

/-- Endpoint classification with the alternatives prioritized: the pure
right-end exception is returned only together with maximality at that end. -/
theorem exists_hook_or_cohookDeletion_or_isPurePositive_startsOnPeak
    (hR : IsAdmissible R) (C : Word R) :
    (∃ D : Word R, Nonempty (HookExtension C D)) ∨
      (∃ D : Word R, Nonempty (CohookDeletion C D)) ∨
        (C.IsPurePositive hR ∧ C.StartsOnPeak) := by
  classical
  by_cases hpeak : C.StartsOnPeak
  · rcases isPurePositive_or_cohookFactorization hR C with
      hpure | hfactor
    · exact Or.inr (Or.inr ⟨hpure, hpeak⟩)
    · obtain ⟨F⟩ := hfactor
      exact Or.inr (Or.inl ⟨F.base, ⟨F.toCohookDeletion hpeak⟩⟩)
  · obtain ⟨D, hhook⟩ := (exists_hook_iff_not_startsOnPeak hR C).2 hpeak
    exact Or.inl ⟨D, hhook⟩

/-- The reversed prioritized endpoint classification: the pure left-end
exception is returned only together with maximality at that end. -/
theorem exists_leftHook_or_leftCohookDeletion_or_isPureNegative_endsOnPeak
    (hR : IsAdmissible R) (C : Word R) :
    Nonempty (LeftHookExtension C) ∨
      (∃ D : Word R, Nonempty (LeftCohookDeletion C D)) ∨
        (C.IsPureNegative hR ∧ C.EndsOnPeak) := by
  rcases
      exists_hook_or_cohookDeletion_or_isPurePositive_startsOnPeak
        hR C.reverse with
    ⟨D, ⟨hook⟩⟩ | ⟨D, ⟨deletion⟩⟩ | ⟨hpure, hpeak⟩
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
  · exact Or.inr (Or.inr ⟨hpure, hpeak⟩)

end Word
end StringWord
end MagnitudeConjecture.BoundQuiver
