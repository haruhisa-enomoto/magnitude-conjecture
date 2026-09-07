import MagnitudeConjecture.Algebra.StringDetectorBoundary
import MagnitudeConjecture.Algebra.StringDetectorFiniteIndex

/-!
# Extending endpoint-polarized detector words

The ordered-word filtration grows a word at its source endpoint.  This file
packages its two legal one-letter extensions: a compatible incoming arrow is
prefixed positively, while a compatible outgoing arrow is prefixed with its
formal inverse.  Both operations preserve the target polarization and
increase word length strictly.
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
variable {S : P.ArrowPolarization} {u : Q} {t : Bool}

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
private theorem signedPathSigns_length
    {x y : Quiver.Symmetrify Q}
    (p : @Quiver.Path (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) x y) :
    (signedPathSigns p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [signedPathSigns, ih]

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
private theorem exists_eq_comp_positive_of_signedPathSigns_eq_false_cons
    {x y : Q} (p : SignedPath x y) (tail : List Bool)
    (hsigns : signedPathSigns p = false :: tail) :
    ∃ (z : Q) (pref : SignedPath x z) (a : z ⟶ y),
      p = pref.comp (positiveArrow a).toPath := by
  cases p with
  | nil => simp [signedPathSigns] at hsigns
  | @cons z y pref e =>
      change Q at z
      cases e with
      | inl a => exact ⟨z, pref, a, rfl⟩
      | inr a => simp [signedPathSigns] at hsigns

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
private theorem exists_eq_comp_negative_of_signedPathSigns_eq_true_cons
    {x y : Q} (p : SignedPath x y) (tail : List Bool)
    (hsigns : signedPathSigns p = true :: tail) :
    ∃ (z : Q) (pref : SignedPath x z) (a : y ⟶ z),
      p = pref.comp (negativeArrow a).toPath := by
  cases p with
  | nil => simp [signedPathSigns] at hsigns
  | @cons z y pref e =>
      change Q at z
      cases e with
      | inl a => simp [signedPathSigns] at hsigns
      | inr a => exact ⟨z, pref, a, rfl⟩

/-- Prefixing a signed letter with the required opposite boundary sign
preserves the target sign of an endpoint word. -/
private theorem signedPathTargetSignOr_prepend_eq
    {x y z : Q} (e : SignedArrow x y) (p : SignedPath y z)
    (htarget : signedPathTargetSignOr S t p = t)
    (hsource : signedPathSourceSignOr S (Bool.not t) p =
      Bool.not (signedArrowTargetSign S e)) :
    signedPathTargetSignOr S t (e.toPath.comp p) = t := by
  cases p with
  | nil =>
      simp only [signedPathSourceSignOr, signedPathSourceSign_nil,
        Option.getD_none] at hsource
      simp only [Quiver.Path.comp_nil, signedPathTargetSignOr]
      exact (Bool.involutive_not.injective hsource).symm
  | cons p f =>
      simpa only [Quiver.Path.comp_cons,
        signedPathTargetSignOr, signedPathTargetSign_cons,
        Option.getD_some] using htarget

/-- Removing the first letter of a polarized path preserves its target
sign. -/
private theorem signedPathTargetSignOr_tail_eq
    {x y z : Q} (e : SignedArrow x y) (p : SignedPath y z)
    (htarget : signedPathTargetSignOr S t (e.toPath.comp p) = t) :
    signedPathTargetSignOr S t p = t := by
  cases p with
  | nil => rfl
  | cons p f =>
      simpa only [Quiver.Path.comp_cons, signedPathTargetSignOr,
        signedPathTargetSign_cons, Option.getD_some] using htarget

/-- The tail left after removing the first letter has the boundary sign
required to regard that letter as a legal source extension. -/
private theorem signedPathSourceSignOr_tail_eq
    {x y z : Q} (e : SignedArrow x y) (p : SignedPath y z)
    (hstring : IsString P.toPresentation.relations (e.toPath.comp p))
    (htarget : signedPathTargetSignOr S t (e.toPath.comp p) = t) :
    signedPathSourceSignOr S (Bool.not t) p =
      Bool.not (signedArrowTargetSign S e) := by
  cases p with
  | nil =>
      have he : signedArrowTargetSign S e = t := by
        rw [Quiver.Path.comp_nil] at htarget
        change (some (signedArrowTargetSign S e)).getD t = t at htarget
        simpa using htarget
      simp [signedPathSourceSignOr, he]
  | cons p f =>
      rw [signedPathSourceSignOr,
        signedPathSourceSign_eq_not_targetSign_of_isString_prepend
          S e (Quiver.Path.cons p f) (by simp) hstring]
      rfl

/-- The target sign of a composite path is already the target sign of its
right-hand tail, with the fixed polarization handling an empty tail. -/
private theorem signedPathTargetSignOr_comp_tail_eq
    {w x y : Q} (pref : SignedPath w x) (tail : SignedPath x y)
    (htarget : signedPathTargetSignOr S t (pref.comp tail) = t) :
    signedPathTargetSignOr S t tail = t := by
  cases tail with
  | nil => rfl
  | cons tail e =>
      simpa only [Quiver.Path.comp_cons, signedPathTargetSignOr,
        signedPathTargetSign_cons, Option.getD_some] using htarget

namespace EndpointWord

/-- The signs of a word read from its fixed target back toward its source.
Source extension appends one Boolean to this list. -/
def routeSigns (C : EndpointWord S u t) : List Bool :=
  signedPathSigns C.path

@[simp]
theorem routeSigns_length (C : EndpointWord S u t) :
    C.routeSigns.length = C.word.length := by
  exact signedPathSigns_length C.path

/-- Prefix the compatible incoming ordinary arrow to an endpoint word. -/
def prependIncoming (C : EndpointWord S u t)
    (inc : C.IncomingExtension) : EndpointWord S u t where
  source := inc.1.1
  path := (positiveArrow inc.1.2).toPath.comp C.path
  isString := inc.2.1
  targetSign_eq := signedPathTargetSignOr_prepend_eq
    (positiveArrow inc.1.2) C.path C.targetSign_eq inc.2.2

/-- Prefix the formal inverse of the compatible outgoing ordinary arrow to
an endpoint word. -/
def prependOutgoingInverse (C : EndpointWord S u t)
    (out : C.OutgoingInverseExtension) : EndpointWord S u t where
  source := out.1.1
  path := (negativeArrow out.1.2).toPath.comp C.path
  isString := out.2.1
  targetSign_eq := signedPathTargetSignOr_prepend_eq
    (negativeArrow out.1.2) C.path C.targetSign_eq out.2.2

@[simp]
theorem prependIncoming_path (C : EndpointWord S u t)
    (inc : C.IncomingExtension) :
    (C.prependIncoming inc).path =
      (positiveArrow inc.1.2).toPath.comp C.path :=
  rfl

@[simp]
theorem prependOutgoingInverse_path (C : EndpointWord S u t)
    (out : C.OutgoingInverseExtension) :
    (C.prependOutgoingInverse out).path =
      (negativeArrow out.1.2).toPath.comp C.path :=
  rfl

@[simp]
theorem prependIncoming_length (C : EndpointWord S u t)
    (inc : C.IncomingExtension) :
    (C.prependIncoming inc).word.length = C.word.length + 1 := by
  change ((positiveArrow inc.1.2).toPath.comp C.path).length =
    C.path.length + 1
  simp [Nat.add_comm]

@[simp]
theorem prependOutgoingInverse_length (C : EndpointWord S u t)
    (out : C.OutgoingInverseExtension) :
    (C.prependOutgoingInverse out).word.length = C.word.length + 1 := by
  change ((negativeArrow out.1.2).toPath.comp C.path).length =
    C.path.length + 1
  simp [Nat.add_comm]

@[simp]
theorem routeSigns_prependIncoming (C : EndpointWord S u t)
    (inc : C.IncomingExtension) :
    (C.prependIncoming inc).routeSigns = C.routeSigns ++ [false] := by
  let a : inc.1.1 ⟶ C.source := inc.1.2
  change signedPathSigns ((positiveArrow a).toPath.comp C.path) =
    signedPathSigns C.path ++ [false]
  rw [signedPathSigns_comp]
  rfl

@[simp]
theorem routeSigns_prependOutgoingInverse (C : EndpointWord S u t)
    (out : C.OutgoingInverseExtension) :
    (C.prependOutgoingInverse out).routeSigns = C.routeSigns ++ [true] := by
  let a : C.source ⟶ out.1.1 := out.1.2
  change signedPathSigns ((negativeArrow a).toPath.comp C.path) =
    signedPathSigns C.path ++ [true]
  rw [signedPathSigns_comp]
  rfl

theorem prependIncoming_ne (C : EndpointWord S u t)
    (inc : C.IncomingExtension) : C.prependIncoming inc ≠ C := by
  intro h
  have hlength := congrArg (fun D : EndpointWord S u t ↦ D.word.length) h
  simp at hlength

theorem prependOutgoingInverse_ne (C : EndpointWord S u t)
    (out : C.OutgoingInverseExtension) : C.prependOutgoingInverse out ≠ C := by
  intro h
  have hlength := congrArg (fun D : EndpointWord S u t ↦ D.word.length) h
  simp at hlength

/-- The interval of a positive source extension lies entirely below the
lower endpoint of its parent interval. -/
theorem prependIncoming_upperSubspace_le_lowerSubspace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) (inc : C.IncomingExtension) :
    upperSubspace N (C.prependIncoming inc) ≤ lowerSubspace N C := by
  classical
  let hinc : Nonempty C.IncomingExtension := ⟨inc⟩
  have hchosen : Classical.choice hinc = inc :=
    @Subsingleton.elim _ C.incomingExtension_subsingleton _ _
  let a : inc.1.1 ⟶ C.source := inc.1.2
  unfold upperSubspace lowerSubspace
  change signedPathSubspace N ((positiveArrow a).toPath.comp C.path)
      (upperBoundarySubspace N (C.prependIncoming inc)) ≤
    signedPathSubspace N C.path (lowerBoundarySubspace N C)
  rw [signedPathSubspace_comp N (positiveArrow a).toPath C.path,
    signedPathSubspace_toPath]
  apply signedPathSubspace_mono N C.path
  calc
    signedArrowSubspace N (positiveArrow a)
        (upperBoundarySubspace N (C.prependIncoming inc)) ≤
        signedArrowSubspace N (positiveArrow a) ⊤ :=
      signedArrowSubspace_mono N _ le_top
    _ = lowerBoundarySubspace N C := by
      simp only [signedArrowSubspace_positive, lowerBoundarySubspace,
        hinc, dite_true]
      rw [hchosen]

/-- The interval of a negative source extension lies entirely above the
upper endpoint of its parent interval. -/
theorem upperSubspace_le_prependOutgoingInverse_lowerSubspace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) (out : C.OutgoingInverseExtension) :
    upperSubspace N C ≤
      lowerSubspace N (C.prependOutgoingInverse out) := by
  classical
  let hout : Nonempty C.OutgoingInverseExtension := ⟨out⟩
  have hchosen : Classical.choice hout = out :=
    @Subsingleton.elim _ C.outgoingInverseExtension_subsingleton _ _
  let a : C.source ⟶ out.1.1 := out.1.2
  unfold upperSubspace lowerSubspace
  change signedPathSubspace N C.path (upperBoundarySubspace N C) ≤
    signedPathSubspace N ((negativeArrow a).toPath.comp C.path)
      (lowerBoundarySubspace N (C.prependOutgoingInverse out))
  rw [signedPathSubspace_comp N (negativeArrow a).toPath C.path,
    signedPathSubspace_toPath]
  apply signedPathSubspace_mono N C.path
  calc
    upperBoundarySubspace N C =
        signedArrowSubspace N (negativeArrow a) ⊥ := by
      simp only [upperBoundarySubspace, hout, dite_true,
        signedArrowSubspace_negative]
      rw [hchosen]
    _ ≤ signedArrowSubspace N (negativeArrow a)
        (lowerBoundarySubspace N (C.prependOutgoingInverse out)) :=
      signedArrowSubspace_mono N _ bot_le

/-- Every word whose path reaches the positive source extension of `C` after
an arbitrary source prefix has its whole interval below `C⁻`. -/
theorem upperSubspace_le_lowerSubspace_of_sourcePrefix_prependIncoming
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C E : EndpointWord S u t) (inc : C.IncomingExtension)
    (pref : SignedPath E.source inc.1.1)
    (hpath : E.path = pref.comp
      ((positiveArrow inc.1.2).toPath.comp C.path)) :
    upperSubspace N E ≤ lowerSubspace N C := by
  classical
  let hinc : Nonempty C.IncomingExtension := ⟨inc⟩
  have hchosen : Classical.choice hinc = inc :=
    @Subsingleton.elim _ C.incomingExtension_subsingleton _ _
  let a : inc.1.1 ⟶ C.source := inc.1.2
  unfold upperSubspace lowerSubspace
  change signedPathSubspace N E.path (upperBoundarySubspace N E) ≤
    signedPathSubspace N C.path (lowerBoundarySubspace N C)
  rw [hpath, signedPathSubspace_comp N pref
      ((positiveArrow a).toPath.comp C.path),
    signedPathSubspace_comp N (positiveArrow a).toPath C.path,
    signedPathSubspace_toPath]
  apply signedPathSubspace_mono N C.path
  calc
    signedArrowSubspace N (positiveArrow a)
        (signedPathSubspace N pref (upperBoundarySubspace N E)) ≤
        signedArrowSubspace N (positiveArrow a) ⊤ :=
      signedArrowSubspace_mono N _ le_top
    _ = lowerBoundarySubspace N C := by
      simp only [signedArrowSubspace_positive, lowerBoundarySubspace,
        hinc, dite_true]
      rw [hchosen]

/-- Every word whose path reaches the inverse source extension of `C` after
an arbitrary source prefix has its whole interval above `C⁺`. -/
theorem upperSubspace_le_lowerSubspace_of_sourcePrefix_prependOutgoingInverse
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C E : EndpointWord S u t) (out : C.OutgoingInverseExtension)
    (pref : SignedPath E.source out.1.1)
    (hpath : E.path = pref.comp
      ((negativeArrow out.1.2).toPath.comp C.path)) :
    upperSubspace N C ≤ lowerSubspace N E := by
  classical
  let hout : Nonempty C.OutgoingInverseExtension := ⟨out⟩
  have hchosen : Classical.choice hout = out :=
    @Subsingleton.elim _ C.outgoingInverseExtension_subsingleton _ _
  let a : C.source ⟶ out.1.1 := out.1.2
  unfold upperSubspace lowerSubspace
  change signedPathSubspace N C.path (upperBoundarySubspace N C) ≤
    signedPathSubspace N E.path (lowerBoundarySubspace N E)
  rw [hpath, signedPathSubspace_comp N pref
      ((negativeArrow a).toPath.comp C.path),
    signedPathSubspace_comp N (negativeArrow a).toPath C.path,
    signedPathSubspace_toPath]
  apply signedPathSubspace_mono N C.path
  calc
    upperBoundarySubspace N C =
        signedArrowSubspace N (negativeArrow a) ⊥ := by
      simp only [upperBoundarySubspace, hout, dite_true,
        signedArrowSubspace_negative]
      rw [hchosen]
    _ ≤ signedArrowSubspace N (negativeArrow a)
        (signedPathSubspace N pref (lowerBoundarySubspace N E)) :=
      signedArrowSubspace_mono N _ bot_le

/-- Every nontrivial endpoint word is obtained, according to its first-letter
sign, from a shorter endpoint word by one of the two source extensions. -/
theorem exists_parent_extension (C : EndpointWord S u t)
    (hC : 0 < C.word.length) :
    (∃ (D : EndpointWord S u t) (inc : D.IncomingExtension),
        C = D.prependIncoming inc) ∨
      ∃ (D : EndpointWord S u t) (out : D.OutgoingInverseExtension),
        C = D.prependOutgoingInverse out := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hC)
  obtain ⟨v, e, tail, htailLength, hpath⟩ :=
    C.path.eq_toPath_comp_of_length_eq_succ hn
  change Q at v
  have htailString : IsString P.toPresentation.relations tail := by
    apply IsString.of_contiguousSubpath P.toPresentation.relations C.isString
    refine ⟨e.toPath, Quiver.Path.nil, ?_⟩
    simpa only [Quiver.Path.comp_nil] using hpath
  have htargetWhole :
      signedPathTargetSignOr S t (e.toPath.comp tail) = t := by
    rw [← hpath]
    exact C.targetSign_eq
  have hcompositeString :
      IsString P.toPresentation.relations (e.toPath.comp tail) := by
    rw [← hpath]
    exact C.isString
  let D : EndpointWord S u t := {
    source := v
    path := tail
    isString := htailString
    targetSign_eq := signedPathTargetSignOr_tail_eq
      (S := S) e tail htargetWhole }
  have hsource : D.sourceSign =
      Bool.not (signedArrowTargetSign S e) := by
    exact signedPathSourceSignOr_tail_eq (P := P) (S := S) e tail
      (by rw [← hpath]; exact C.isString) htargetWhole
  cases e with
  | inl a =>
      left
      let inc : D.IncomingExtension :=
        ⟨⟨C.source, a⟩, by exact hcompositeString,
          by
            change D.sourceSign = Bool.not (S.targetSign a) at hsource
            exact hsource⟩
      refine ⟨D, inc, ?_⟩
      apply EndpointWord.word_injective S
      apply Word.ext
      · rfl
      · rfl
      · exact heq_of_eq hpath
  | inr a =>
      right
      let out : D.OutgoingInverseExtension :=
        ⟨⟨C.source, a⟩, by exact hcompositeString,
          by
            change D.sourceSign = Bool.not (S.sourceSign a) at hsource
            exact hsource⟩
      refine ⟨D, out, ?_⟩
      apply EndpointWord.word_injective S
      apply Word.ext
      · rfl
      · rfl
      · exact heq_of_eq hpath

/-- An endpoint word of length zero is the fixed polarized vertex word. -/
theorem eq_vertex_of_word_length_eq_zero (C : EndpointWord S u t)
    (hC : C.word.length = 0) :
    C = EndpointWord.vertex P S u t := by
  rcases C with ⟨source, path, hstring, hsign⟩
  change path.length = 0 at hC
  have hsource : source = u := path.eq_of_length_zero hC
  subst source
  have hpath : path = Quiver.Path.nil := path.eq_nil_of_length_zero hC
  subst path
  rfl

/-- For fixed target and polarization, the signs read from target to source
determine the whole endpoint word. -/
theorem routeSigns_injective :
    Function.Injective (routeSigns : EndpointWord S u t → List Bool) := by
  intro C
  induction hlength : C.word.length using Nat.strong_induction_on
      generalizing C with
  | h n ih =>
      intro D hsigns
      have hDlength : D.word.length = n := by
        rw [← D.routeSigns_length, ← hsigns, C.routeSigns_length,
          hlength]
      by_cases hn : n = 0
      · rw [C.eq_vertex_of_word_length_eq_zero (by omega),
          D.eq_vertex_of_word_length_eq_zero (by omega)]
      · have hCpos : 0 < C.word.length := by omega
        have hDpos : 0 < D.word.length := by omega
        rcases C.exists_parent_extension hCpos with
          ⟨C₀, incC, rfl⟩ | ⟨C₀, outC, rfl⟩ <;>
          rcases D.exists_parent_extension hDpos with
            ⟨D₀, incD, rfl⟩ | ⟨D₀, outD, rfl⟩
        · simp only [routeSigns_prependIncoming] at hsigns
          have hparents : C₀.routeSigns = D₀.routeSigns :=
            List.append_cancel_right hsigns
          rw [prependIncoming_length] at hlength
          have hparentLength : C₀.word.length < n := by omega
          have hparent : C₀ = D₀ :=
            ih C₀.word.length hparentLength rfl hparents
          subst D₀
          have hinc : incC = incD :=
            @Subsingleton.elim _ C₀.incomingExtension_subsingleton _ _
          subst incD
          rfl
        · simp only [routeSigns_prependIncoming,
            routeSigns_prependOutgoingInverse] at hsigns
          have hreversed := congrArg List.reverse hsigns
          simp only [List.reverse_append, List.reverse_singleton,
            List.singleton_append] at hreversed
          have hfalse : false = true := (List.cons.inj hreversed).1
          cases hfalse
        · simp only [routeSigns_prependOutgoingInverse,
            routeSigns_prependIncoming] at hsigns
          have hreversed := congrArg List.reverse hsigns
          simp only [List.reverse_append, List.reverse_singleton,
            List.singleton_append] at hreversed
          have htrue : true = false := (List.cons.inj hreversed).1
          cases htrue
        · simp only [routeSigns_prependOutgoingInverse] at hsigns
          have hparents : C₀.routeSigns = D₀.routeSigns :=
            List.append_cancel_right hsigns
          rw [prependOutgoingInverse_length] at hlength
          have hparentLength : C₀.word.length < n := by omega
          have hparent : C₀ = D₀ :=
            ih C₀.word.length hparentLength rfl hparents
          subst D₀
          have hout : outC = outD :=
            @Subsingleton.elim _ C₀.outgoingInverseExtension_subsingleton _ _
          subst outD
          rfl

/-- If the route-sign word of `C` is an initial segment of that of `D`, then
the literal path of `C` is a target-side suffix of the literal path of `D`.
The extra source-side path is returned explicitly. -/
theorem exists_sourcePrefix_of_routeSigns_eq_append
    (C D : EndpointWord S u t) (suffix : List Bool)
    (hsigns : D.routeSigns = C.routeSigns ++ suffix) :
    ∃ pref : SignedPath D.source C.source,
      D.path = pref.comp C.path ∧ signedPathSigns pref = suffix := by
  have hlength := congrArg List.length hsigns
  simp only [routeSigns_length, List.length_append] at hlength
  have hsuffix_le : suffix.length ≤ D.path.length := by
    change suffix.length ≤ D.word.length
    omega
  obtain ⟨v, pref, tail, hfactor, hprefLength⟩ :=
    D.path.exists_eq_comp_of_le_length hsuffix_le
  change Q at v
  have htailLength : tail.length = C.word.length := by
    have htotalLength := congrArg Quiver.Path.length hfactor
    simp only [Quiver.Path.length_comp] at htotalLength
    change D.word.length = pref.length + tail.length at htotalLength
    omega
  have htailString : IsString P.toPresentation.relations tail := by
    apply IsString.of_contiguousSubpath P.toPresentation.relations D.isString
    refine ⟨pref, Quiver.Path.nil, ?_⟩
    simpa only [Quiver.Path.comp_nil] using hfactor
  have htargetFactor :
      signedPathTargetSignOr S t (pref.comp tail) = t := by
    rw [← hfactor]
    exact D.targetSign_eq
  let T : EndpointWord S u t := {
    source := v
    path := tail
    isString := htailString
    targetSign_eq := signedPathTargetSignOr_comp_tail_eq
      (S := S) pref tail htargetFactor }
  have hfactorSigns :
      T.routeSigns ++ signedPathSigns pref =
        C.routeSigns ++ suffix := by
    calc
      T.routeSigns ++ signedPathSigns pref = D.routeSigns := by
        rw [routeSigns, routeSigns, hfactor, signedPathSigns_comp]
      _ = C.routeSigns ++ suffix := hsigns
  have hrouteLength : T.routeSigns.length = C.routeSigns.length := by
    rw [T.routeSigns_length, C.routeSigns_length]
    exact htailLength
  have hTCSigns : T.routeSigns = C.routeSigns :=
    (List.append_inj hfactorSigns hrouteLength).1
  have hprefSigns : signedPathSigns pref = suffix :=
    (List.append_inj hfactorSigns hrouteLength).2
  have hTC : T = C := routeSigns_injective hTCSigns
  subst C
  exact ⟨pref, hfactor, hprefSigns⟩

/-- Every initial segment of an endpoint word's route signs is itself
realized by a target-side endpoint word, and the remaining signs come from
the explicit source prefix. -/
theorem exists_endpointWord_of_routeSigns_eq_append
    (E : EndpointWord S u t) (base suffix : List Bool)
    (hsigns : E.routeSigns = base ++ suffix) :
    ∃ (C : EndpointWord S u t) (pref : SignedPath E.source C.source),
      C.routeSigns = base ∧ E.path = pref.comp C.path ∧
        signedPathSigns pref = suffix := by
  have hlength := congrArg List.length hsigns
  simp only [routeSigns_length, List.length_append] at hlength
  have hsuffix_le : suffix.length ≤ E.path.length := by
    change suffix.length ≤ E.word.length
    omega
  obtain ⟨v, pref, tail, hfactor, hprefLength⟩ :=
    E.path.exists_eq_comp_of_le_length hsuffix_le
  change Q at v
  have htailLength : tail.length = base.length := by
    have htotalLength := congrArg Quiver.Path.length hfactor
    simp only [Quiver.Path.length_comp] at htotalLength
    change E.word.length = pref.length + tail.length at htotalLength
    omega
  have htailString : IsString P.toPresentation.relations tail := by
    apply IsString.of_contiguousSubpath P.toPresentation.relations E.isString
    refine ⟨pref, Quiver.Path.nil, ?_⟩
    simpa only [Quiver.Path.comp_nil] using hfactor
  have htargetFactor :
      signedPathTargetSignOr S t (pref.comp tail) = t := by
    rw [← hfactor]
    exact E.targetSign_eq
  let C : EndpointWord S u t := {
    source := v
    path := tail
    isString := htailString
    targetSign_eq := signedPathTargetSignOr_comp_tail_eq
      (S := S) pref tail htargetFactor }
  have hfactorSigns :
      C.routeSigns ++ signedPathSigns pref = base ++ suffix := by
    calc
      C.routeSigns ++ signedPathSigns pref = E.routeSigns := by
        rw [routeSigns, routeSigns, hfactor, signedPathSigns_comp]
      _ = base ++ suffix := hsigns
  have hrouteLength : C.routeSigns.length = base.length := by
    rw [C.routeSigns_length]
    exact htailLength
  exact ⟨C, pref,
    (List.append_inj hfactorSigns hrouteLength).1, hfactor,
    (List.append_inj hfactorSigns hrouteLength).2⟩

/-- Every endpoint word in the positive branch below `C` has its interval
below the lower endpoint of `C`. -/
theorem upperSubspace_le_lowerSubspace_of_routeSigns_eq_append_false
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C E : EndpointWord S u t) (tail : List Bool)
    (hsigns : E.routeSigns = C.routeSigns ++ false :: tail) :
    upperSubspace N E ≤ lowerSubspace N C := by
  obtain ⟨pref, hfactor, hprefSigns⟩ :=
    C.exists_sourcePrefix_of_routeSigns_eq_append E (false :: tail) hsigns
  obtain ⟨y, outer, a, hpref⟩ :=
    exists_eq_comp_positive_of_signedPathSigns_eq_false_cons
      pref tail hprefSigns
  have hfactor' : E.path = outer.comp
      ((positiveArrow a).toPath.comp C.path) := by
    calc
      E.path = pref.comp C.path := hfactor
      _ = (outer.comp (positiveArrow a).toPath).comp C.path := by rw [hpref]
      _ = outer.comp ((positiveArrow a).toPath.comp C.path) := by
        rw [Quiver.Path.comp_assoc]
  have hbranchString : IsString P.toPresentation.relations
      ((positiveArrow a).toPath.comp C.path) := by
    apply IsString.of_contiguousSubpath
      P.toPresentation.relations E.isString
    refine ⟨outer, Quiver.Path.nil, ?_⟩
    simpa only [Quiver.Path.comp_nil] using hfactor'
  have hbranchTarget : signedPathTargetSignOr S t
      ((positiveArrow a).toPath.comp C.path) = t := by
    apply signedPathTargetSignOr_comp_tail_eq
      (S := S) outer ((positiveArrow a).toPath.comp C.path)
    rw [← hfactor']
    exact E.targetSign_eq
  have hsource : C.sourceSign = Bool.not (S.targetSign a) := by
    exact signedPathSourceSignOr_tail_eq (P := P) (S := S)
      (positiveArrow a) C.path hbranchString hbranchTarget
  let inc : C.IncomingExtension :=
    ⟨⟨y, a⟩, hbranchString, hsource⟩
  exact upperSubspace_le_lowerSubspace_of_sourcePrefix_prependIncoming
    N C E inc outer hfactor'

/-- Every endpoint word in the inverse branch above `C` has its interval
above the upper endpoint of `C`. -/
theorem upperSubspace_le_lowerSubspace_of_routeSigns_eq_append_true
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C E : EndpointWord S u t) (tail : List Bool)
    (hsigns : E.routeSigns = C.routeSigns ++ true :: tail) :
    upperSubspace N C ≤ lowerSubspace N E := by
  obtain ⟨pref, hfactor, hprefSigns⟩ :=
    C.exists_sourcePrefix_of_routeSigns_eq_append E (true :: tail) hsigns
  obtain ⟨y, outer, a, hpref⟩ :=
    exists_eq_comp_negative_of_signedPathSigns_eq_true_cons
      pref tail hprefSigns
  have hfactor' : E.path = outer.comp
      ((negativeArrow a).toPath.comp C.path) := by
    calc
      E.path = pref.comp C.path := hfactor
      _ = (outer.comp (negativeArrow a).toPath).comp C.path := by rw [hpref]
      _ = outer.comp ((negativeArrow a).toPath.comp C.path) := by
        rw [Quiver.Path.comp_assoc]
  have hbranchString : IsString P.toPresentation.relations
      ((negativeArrow a).toPath.comp C.path) := by
    apply IsString.of_contiguousSubpath
      P.toPresentation.relations E.isString
    refine ⟨outer, Quiver.Path.nil, ?_⟩
    simpa only [Quiver.Path.comp_nil] using hfactor'
  have hbranchTarget : signedPathTargetSignOr S t
      ((negativeArrow a).toPath.comp C.path) = t := by
    apply signedPathTargetSignOr_comp_tail_eq
      (S := S) outer ((negativeArrow a).toPath.comp C.path)
    rw [← hfactor']
    exact E.targetSign_eq
  have hsource : C.sourceSign = Bool.not (S.sourceSign a) := by
    exact signedPathSourceSignOr_tail_eq (P := P) (S := S)
      (negativeArrow a) C.path hbranchString hbranchTarget
  let out : C.OutgoingInverseExtension :=
    ⟨⟨y, a⟩, hbranchString, hsource⟩
  exact
    upperSubspace_le_lowerSubspace_of_sourcePrefix_prependOutgoingInverse
      N C E out outer hfactor'

end EndpointWord

end MagnitudeConjecture.BoundQuiver.StringWord
