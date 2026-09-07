import MagnitudeConjecture.Algebra.StringBoundQuiver
import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Deterministic path continuations in string presentations

The special-biserial continuation conditions make every nonzero path beyond
a fixed initial arrow deterministic.  This file packages that statement with
path length retained, which is the combinatorial input for the uniserial
arrow ideals and string modules used in the frozen manuscript.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace SpecialBiserialPresentation

/-- The arrows which can follow `a` without making the two-arrow path zero. -/
abbrev RightContinuationArrow
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) :=
  {b : Quiver.Star y //
    arrowMap P.toPresentation.relations b.2 ≫
        arrowMap P.toPresentation.relations a ≠ 0}

/-- The arrows which can precede `a` without making the two-arrow path zero. -/
abbrev LeftContinuationArrow
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) :=
  {c : Quiver.Costar x //
    arrowMap P.toPresentation.relations a ≫
        arrowMap P.toPresentation.relations c.2 ≠ 0}

/-- There is at most one nonzero right continuation of an arrow. -/
theorem rightContinuationArrow_subsingleton
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) :
    Subsingleton (P.RightContinuationArrow a) := by
  letI : Fintype (P.RightContinuationArrow a) := Fintype.ofFinite _
  apply Fintype.card_le_one_iff_subsingleton.mp
  simpa only [Nat.card_eq_fintype_card] using P.continuation_right_le_one a

/-- There is at most one nonzero left continuation of an arrow. -/
theorem leftContinuationArrow_subsingleton
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) :
    Subsingleton (P.LeftContinuationArrow a) := by
  letI : Fintype (P.LeftContinuationArrow a) := Fintype.ofFinite _
  apply Fintype.card_le_one_iff_subsingleton.mp
  simpa only [Nat.card_eq_fintype_card] using P.continuation_left_le_one a

/-- All nonzero path continuations after `a`, with endpoint retained. -/
abbrev RightContinuationPath
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) :=
  {q : Σ z : Q, Quiver.Path y z //
    pathMap P.toPresentation.relations q.2 ≫
        arrowMap P.toPresentation.relations a ≠ 0}

/-- Concatenating the fixed initial arrow embeds its nonzero continuations
into the surviving paths of the quotient. -/
def rightContinuationPathToSurviving
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) :
    P.RightContinuationPath a →
      Σ z : Q, SurvivingPath P.toPresentation.relations x z :=
  fun q ↦
    ⟨q.1.1, ⟨a.toPath.comp q.1.2, by
      rw [← pathMap_comp]
      exact q.2⟩⟩

/-- Distinct continuations remain distinct after adjoining their common
initial arrow. -/
theorem rightContinuationPathToSurviving_injective
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) :
    Function.Injective (P.rightContinuationPathToSurviving a) := by
  rintro ⟨⟨z, p⟩, hp⟩ ⟨⟨w, q⟩, hq⟩ h
  change
    (⟨z, ⟨a.toPath.comp p, _⟩⟩ :
        Σ t : Q, SurvivingPath P.toPresentation.relations x t) =
      ⟨w, ⟨a.toPath.comp q, _⟩⟩ at h
  injection h with hzw hpq
  subst w
  have hpq' : a.toPath.comp p = a.toPath.comp q := by
    exact congrArg Subtype.val (eq_of_heq hpq)
  have : p = q := Quiver.Path.comp_injective_right a.toPath hpq'
  subst q
  rfl

/-- Admissibility makes the complete set of nonzero continuations of one
arrow finite. -/
theorem rightContinuationPath_finite
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) :
    Finite (P.RightContinuationPath a) := by
  letI (z : Q) : Finite
      (SurvivingPath P.toPresentation.relations x z) :=
    survivingPathFiniteOfAdmissible P.toPresentation.relations
      P.toPresentation.admissible x z
  exact Finite.of_injective (P.rightContinuationPathToSurviving a)
    (P.rightContinuationPathToSurviving_injective a)

/-- A nonzero path of prescribed additional length after the arrow `a`.
The endpoint is retained in the sigma type. -/
abbrev RightContinuationPathAtLength
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (n : ℕ) :=
  {q : Σ z : Q, Quiver.Path y z //
    q.2.length = n ∧
      pathMap P.toPresentation.relations q.2 ≫
        arrowMap P.toPresentation.relations a ≠ 0}

/-- Beyond a fixed initial arrow, a nonzero path is uniquely determined by
its additional length. -/
theorem rightContinuationPathAtLength_subsingleton
    (P : SpecialBiserialPresentation k A Q) :
    ∀ (n : ℕ) {x y : Q} (a : x ⟶ y),
      Subsingleton (P.RightContinuationPathAtLength a n) := by
  intro n
  induction n with
  | zero =>
      intro x y a
      constructor
      rintro ⟨⟨z, p⟩, hp, _⟩ ⟨⟨w, q⟩, hq, _⟩
      have hzy : y = z := p.eq_of_length_zero hp
      have hwy : y = w := q.eq_of_length_zero hq
      subst z
      subst w
      have hpNil : p = Quiver.Path.nil := p.eq_nil_of_length_zero hp
      have hqNil : q = Quiver.Path.nil := q.eq_nil_of_length_zero hq
      subst p
      subst q
      rfl
  | succ n ih =>
      intro x y a
      constructor
      rintro ⟨⟨z, p⟩, hp, hp0⟩ ⟨⟨w, q⟩, hq, hq0⟩
      obtain ⟨c, b, r, hr, rfl⟩ :=
        p.eq_toPath_comp_of_length_eq_succ hp
      obtain ⟨d, b', s, hs, rfl⟩ :=
        q.eq_toPath_comp_of_length_eq_succ hq
      change
        pathMap P.toPresentation.relations (b.toPath.comp r) ≫
            arrowMap P.toPresentation.relations a ≠ 0 at hp0
      change
        pathMap P.toPresentation.relations (b'.toPath.comp s) ≫
            arrowMap P.toPresentation.relations a ≠ 0 at hq0
      have hb0 :
          arrowMap P.toPresentation.relations b ≫
              arrowMap P.toPresentation.relations a ≠ 0 := by
        intro hzero
        apply hp0
        rw [← pathMap_comp]
        change
          (pathMap P.toPresentation.relations r ≫
              arrowMap P.toPresentation.relations b) ≫
            arrowMap P.toPresentation.relations a = 0
        rw [Category.assoc, hzero, CategoryTheory.Limits.comp_zero]
      have hb'0 :
          arrowMap P.toPresentation.relations b' ≫
              arrowMap P.toPresentation.relations a ≠ 0 := by
        intro hzero
        apply hq0
        rw [← pathMap_comp]
        change
          (pathMap P.toPresentation.relations s ≫
              arrowMap P.toPresentation.relations b') ≫
            arrowMap P.toPresentation.relations a = 0
        rw [Category.assoc, hzero, CategoryTheory.Limits.comp_zero]
      have hbb' : (⟨c, b⟩ : Quiver.Star y) = ⟨d, b'⟩ := by
        exact congrArg Subtype.val
          (@Subsingleton.elim _ (P.rightContinuationArrow_subsingleton a)
            (⟨⟨c, b⟩, hb0⟩ : P.RightContinuationArrow a)
            (⟨⟨d, b'⟩, hb'0⟩ : P.RightContinuationArrow a))
      cases hbb'
      have hr0 :
          pathMap P.toPresentation.relations r ≫
              arrowMap P.toPresentation.relations b ≠ 0 := by
        intro hzero
        apply hp0
        rw [← pathMap_comp]
        change
          (pathMap P.toPresentation.relations r ≫
              arrowMap P.toPresentation.relations b) ≫
            arrowMap P.toPresentation.relations a = 0
        rw [hzero, CategoryTheory.Limits.zero_comp]
      have hs0 :
          pathMap P.toPresentation.relations s ≫
              arrowMap P.toPresentation.relations b ≠ 0 := by
        intro hzero
        apply hq0
        rw [← pathMap_comp]
        change
          (pathMap P.toPresentation.relations s ≫
              arrowMap P.toPresentation.relations b) ≫
            arrowMap P.toPresentation.relations a = 0
        rw [hzero, CategoryTheory.Limits.zero_comp]
      have hrs :
          (⟨⟨z, r⟩, hr, hr0⟩ :
              P.RightContinuationPathAtLength b n) =
            ⟨⟨w, s⟩, hs, hs0⟩ :=
        @Subsingleton.elim _ (ih b) _ _
      cases hrs
      rfl

/-- The set of nonzero right continuations of any fixed length has cardinality
at most one. -/
theorem natCard_rightContinuationPathAtLength_le_one
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (n : ℕ) :
    Nat.card (P.RightContinuationPathAtLength a n) ≤ 1 := by
  letI : Finite (P.RightContinuationPath a) :=
    P.rightContinuationPath_finite a
  let forgetLength : P.RightContinuationPathAtLength a n →
      P.RightContinuationPath a := fun q ↦ ⟨q.1, q.2.2⟩
  letI : Finite (P.RightContinuationPathAtLength a n) :=
    Finite.of_injective forgetLength (by
      intro p q hpq
      apply Subtype.ext
      exact congrArg
        (fun t : P.RightContinuationPath a ↦ t.1) hpq)
  exact Finite.card_le_one_iff_subsingleton.mpr
    (P.rightContinuationPathAtLength_subsingleton n a)

/-- Length embeds the complete finite set of nonzero right continuations into
the natural numbers.  Thus those continuations form one chain, with no
branching at any radical layer. -/
def rightContinuationLengthEmbedding
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) :
    P.RightContinuationPath a ↪ ℕ where
  toFun q := q.1.2.length
  inj' := by
    intro p q hpq
    have h :
        (⟨p.1, rfl, p.2⟩ :
            P.RightContinuationPathAtLength a p.1.2.length) =
          ⟨q.1, hpq.symm, q.2⟩ :=
      @Subsingleton.elim _
        (P.rightContinuationPathAtLength_subsingleton p.1.2.length a) _ _
    apply Subtype.ext
    exact congrArg
      (fun t : P.RightContinuationPathAtLength a p.1.2.length ↦ t.1) h

/-- A longer surviving right continuation factors through every shorter
one.  The factor is the final segment between their endpoints. -/
theorem rightContinuationPath_factor_of_length_le
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y)
    (p q : P.RightContinuationPath a)
    (h : p.1.2.length ≤ q.1.2.length) :
    ∃ r : Quiver.Path p.1.1 q.1.1,
      q.1.2 = p.1.2.comp r := by
  obtain ⟨v, s, r, hq, hs⟩ :=
    q.1.2.exists_eq_comp_of_le_length h
  have hs0 :
      pathMap P.toPresentation.relations s ≫
          arrowMap P.toPresentation.relations a ≠ 0 := by
    intro hzero
    apply q.2
    rw [hq, ← pathMap_comp]
    rw [Category.assoc, hzero, CategoryTheory.Limits.comp_zero]
  let ps : P.RightContinuationPathAtLength a p.1.2.length :=
    ⟨p.1, rfl, p.2⟩
  let qs : P.RightContinuationPathAtLength a p.1.2.length :=
    ⟨⟨v, s⟩, hs, hs0⟩
  have hpq : ps = qs :=
    @Subsingleton.elim _
      (P.rightContinuationPathAtLength_subsingleton p.1.2.length a) ps qs
  have hbase : p.1 = (⟨v, s⟩ : Σ z : Q, Quiver.Path y z) :=
    congrArg
      (fun t : P.RightContinuationPathAtLength a p.1.2.length ↦ t.1) hpq
  have hv : p.1.1 = v := (Sigma.ext_iff.mp hbase).1
  have hps : p.1.2 ≍ s := (Sigma.ext_iff.mp hbase).2
  subst v
  have hpath : p.1.2 = s := eq_of_heq hps
  subst s
  exact ⟨r, hq⟩

/-- Surviving right continuations of `a` with one fixed endpoint. -/
abbrev RightContinuationAt
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q) :=
  {q : Quiver.Path y z //
    pathMap P.toPresentation.relations q ≫
        arrowMap P.toPresentation.relations a ≠ 0}

/-- A fixed-endpoint continuation is in particular a continuation with
varying endpoint. -/
def rightContinuationAtToPath
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q) :
    P.RightContinuationAt a z → P.RightContinuationPath a :=
  fun q ↦ ⟨⟨z, q.1⟩, q.2⟩

/-- Forgetting that the endpoint was fixed is injective. -/
theorem rightContinuationAtToPath_injective
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q) :
    Function.Injective (P.rightContinuationAtToPath a z) := by
  intro p q hpq
  apply Subtype.ext
  have hval := congrArg
    (fun t : P.RightContinuationPath a ↦ t.1) hpq
  injection hval

/-- Fixed-endpoint continuations form a finite type. -/
theorem rightContinuationAt_finite
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q) :
    Finite (P.RightContinuationAt a z) := by
  letI : Finite (P.RightContinuationPath a) :=
    P.rightContinuationPath_finite a
  exact Finite.of_injective (P.rightContinuationAtToPath a z)
    (P.rightContinuationAtToPath_injective a z)

/-- Path length embeds the fixed-endpoint continuation chain into the
natural numbers. -/
def rightContinuationAtLengthEmbedding
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q) :
    P.RightContinuationAt a z ↪ ℕ :=
  (⟨P.rightContinuationAtToPath a z,
      P.rightContinuationAtToPath_injective a z⟩ :
    P.RightContinuationAt a z ↪ P.RightContinuationPath a).trans
    (P.rightContinuationLengthEmbedding a)

/-- At a fixed endpoint, every longer continuation is obtained from every
shorter one by adjoining a loop at that endpoint. -/
theorem rightContinuationAt_factor_of_length_le
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q)
    (p q : P.RightContinuationAt a z)
    (h : p.1.length ≤ q.1.length) :
    ∃ r : Quiver.Path z z, q.1 = p.1.comp r := by
  simpa only [rightContinuationAtToPath] using
    P.rightContinuationPath_factor_of_length_le a
      (P.rightContinuationAtToPath a z p)
      (P.rightContinuationAtToPath a z q) h

/-- A strict increase in continuation length gives a positive-length loop
factor at the common endpoint. -/
theorem rightContinuationAt_factor_of_length_lt
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q)
    (p q : P.RightContinuationAt a z)
    (h : p.1.length < q.1.length) :
    ∃ r : Quiver.Path z z,
      q.1 = p.1.comp r ∧ r.length ≠ 0 := by
  obtain ⟨r, hr⟩ := P.rightContinuationAt_factor_of_length_le a z p q h.le
  refine ⟨r, hr, ?_⟩
  intro hrzero
  have hlength := congrArg Quiver.Path.length hr
  simp only [Quiver.Path.length_comp, hrzero, add_zero] at hlength
  omega

/-- All nonzero path continuations before `a`, with starting vertex retained. -/
abbrev LeftContinuationPath
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) :=
  {p : Σ z : Q, Quiver.Path z x //
    arrowMap P.toPresentation.relations a ≫
        pathMap P.toPresentation.relations p.2 ≠ 0}

/-- Concatenating the fixed final arrow embeds its nonzero left continuations
into the surviving paths of the quotient. -/
def leftContinuationPathToSurviving
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) :
    P.LeftContinuationPath a →
      Σ z : Q, SurvivingPath P.toPresentation.relations z y :=
  fun p ↦
    ⟨p.1.1, ⟨p.1.2.comp a.toPath, by
      rw [← pathMap_comp]
      exact p.2⟩⟩

/-- Distinct left continuations remain distinct after adjoining their common
final arrow. -/
theorem leftContinuationPathToSurviving_injective
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) :
    Function.Injective (P.leftContinuationPathToSurviving a) := by
  rintro ⟨⟨z, p⟩, hp⟩ ⟨⟨w, q⟩, hq⟩ h
  change
    (⟨z, ⟨p.comp a.toPath, _⟩⟩ :
        Σ t : Q, SurvivingPath P.toPresentation.relations t y) =
      ⟨w, ⟨q.comp a.toPath, _⟩⟩ at h
  injection h with hzw hpq
  subst w
  have hpq' : p.comp a.toPath = q.comp a.toPath := by
    exact congrArg Subtype.val (eq_of_heq hpq)
  have : p = q := Quiver.Path.comp_injective_left a.toPath hpq'
  subst q
  rfl

/-- Admissibility makes the complete set of nonzero left continuations of one
arrow finite. -/
theorem leftContinuationPath_finite
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) :
    Finite (P.LeftContinuationPath a) := by
  letI (z : Q) : Finite
      (SurvivingPath P.toPresentation.relations z y) :=
    survivingPathFiniteOfAdmissible P.toPresentation.relations
      P.toPresentation.admissible z y
  exact Finite.of_injective (P.leftContinuationPathToSurviving a)
    (P.leftContinuationPathToSurviving_injective a)

/-- A nonzero path of prescribed additional length before the arrow `a`.
The starting vertex is retained in the sigma type. -/
abbrev LeftContinuationPathAtLength
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (n : ℕ) :=
  {p : Σ z : Q, Quiver.Path z x //
    p.2.length = n ∧
      arrowMap P.toPresentation.relations a ≫
        pathMap P.toPresentation.relations p.2 ≠ 0}

/-- Before a fixed final arrow, a nonzero path is uniquely determined by
its additional length. -/
theorem leftContinuationPathAtLength_subsingleton
    (P : SpecialBiserialPresentation k A Q) :
    ∀ (n : ℕ) {x y : Q} (a : x ⟶ y),
      Subsingleton (P.LeftContinuationPathAtLength a n) := by
  intro n
  induction n with
  | zero =>
      intro x y a
      constructor
      rintro ⟨⟨z, p⟩, hp, _⟩ ⟨⟨w, q⟩, hq, _⟩
      have hzx : z = x := p.eq_of_length_zero hp
      have hwx : w = x := q.eq_of_length_zero hq
      subst z
      subst w
      have hpNil : p = Quiver.Path.nil := p.eq_nil_of_length_zero hp
      have hqNil : q = Quiver.Path.nil := q.eq_nil_of_length_zero hq
      subst p
      subst q
      rfl
  | succ n ih =>
      intro x y a
      constructor
      rintro ⟨⟨z, p⟩, hp, hp0⟩ ⟨⟨w, q⟩, hq, hq0⟩
      cases p with
      | nil => simp at hp
      | @cons c _ r b =>
        cases q with
        | nil => simp at hq
        | @cons d _ s b' =>
          have hr : r.length = n := by simpa using hp
          have hs : s.length = n := by simpa using hq
          change
            arrowMap P.toPresentation.relations a ≫
                pathMap P.toPresentation.relations (r.cons b) ≠ 0 at hp0
          change
            arrowMap P.toPresentation.relations a ≫
                pathMap P.toPresentation.relations (s.cons b') ≠ 0 at hq0
          have hb0 :
              arrowMap P.toPresentation.relations a ≫
                  arrowMap P.toPresentation.relations b ≠ 0 := by
            intro hzero
            apply hp0
            rw [← Quiver.Path.comp_toPath_eq_cons, ← pathMap_comp]
            change
              arrowMap P.toPresentation.relations a ≫
                  (arrowMap P.toPresentation.relations b ≫
                    pathMap P.toPresentation.relations r) = 0
            rw [← Category.assoc, hzero,
              CategoryTheory.Limits.zero_comp]
          have hb'0 :
              arrowMap P.toPresentation.relations a ≫
                  arrowMap P.toPresentation.relations b' ≠ 0 := by
            intro hzero
            apply hq0
            rw [← Quiver.Path.comp_toPath_eq_cons, ← pathMap_comp]
            change
              arrowMap P.toPresentation.relations a ≫
                  (arrowMap P.toPresentation.relations b' ≫
                    pathMap P.toPresentation.relations s) = 0
            rw [← Category.assoc, hzero,
              CategoryTheory.Limits.zero_comp]
          have hbb' : (⟨c, b⟩ : Quiver.Costar x) = ⟨d, b'⟩ := by
            exact congrArg Subtype.val
              (@Subsingleton.elim _ (P.leftContinuationArrow_subsingleton a)
                (⟨⟨c, b⟩, hb0⟩ : P.LeftContinuationArrow a)
                (⟨⟨d, b'⟩, hb'0⟩ : P.LeftContinuationArrow a))
          cases hbb'
          have hr0 :
              arrowMap P.toPresentation.relations b ≫
                  pathMap P.toPresentation.relations r ≠ 0 := by
            intro hzero
            apply hp0
            rw [← Quiver.Path.comp_toPath_eq_cons, ← pathMap_comp]
            change
              arrowMap P.toPresentation.relations a ≫
                  (arrowMap P.toPresentation.relations b ≫
                    pathMap P.toPresentation.relations r) = 0
            rw [hzero, CategoryTheory.Limits.comp_zero]
          have hs0 :
              arrowMap P.toPresentation.relations b ≫
                  pathMap P.toPresentation.relations s ≠ 0 := by
            intro hzero
            apply hq0
            rw [← Quiver.Path.comp_toPath_eq_cons, ← pathMap_comp]
            change
              arrowMap P.toPresentation.relations a ≫
                  (arrowMap P.toPresentation.relations b ≫
                    pathMap P.toPresentation.relations s) = 0
            rw [hzero, CategoryTheory.Limits.comp_zero]
          have hrs :
              (⟨⟨z, r⟩, hr, hr0⟩ :
                  P.LeftContinuationPathAtLength b n) =
                ⟨⟨w, s⟩, hs, hs0⟩ :=
            @Subsingleton.elim _ (ih b) _ _
          cases hrs
          rfl

/-- The set of nonzero left continuations of any fixed length has cardinality
at most one. -/
theorem natCard_leftContinuationPathAtLength_le_one
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (n : ℕ) :
    Nat.card (P.LeftContinuationPathAtLength a n) ≤ 1 := by
  letI : Finite (P.LeftContinuationPath a) :=
    P.leftContinuationPath_finite a
  let forgetLength : P.LeftContinuationPathAtLength a n →
      P.LeftContinuationPath a := fun p ↦ ⟨p.1, p.2.2⟩
  letI : Finite (P.LeftContinuationPathAtLength a n) :=
    Finite.of_injective forgetLength (by
      intro p q hpq
      apply Subtype.ext
      exact congrArg
        (fun t : P.LeftContinuationPath a ↦ t.1) hpq)
  exact Finite.card_le_one_iff_subsingleton.mpr
    (P.leftContinuationPathAtLength_subsingleton n a)

/-- Length embeds the complete finite set of nonzero left continuations into
the natural numbers. -/
def leftContinuationLengthEmbedding
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) :
    P.LeftContinuationPath a ↪ ℕ where
  toFun p := p.1.2.length
  inj' := by
    intro p q hpq
    have h :
        (⟨p.1, rfl, p.2⟩ :
            P.LeftContinuationPathAtLength a p.1.2.length) =
          ⟨q.1, hpq.symm, q.2⟩ :=
      @Subsingleton.elim _
        (P.leftContinuationPathAtLength_subsingleton p.1.2.length a) _ _
    apply Subtype.ext
    exact congrArg
      (fun t : P.LeftContinuationPathAtLength a p.1.2.length ↦ t.1) h

/-- A longer surviving left continuation factors through every shorter one.
The factor is the initial segment between their starting vertices. -/
theorem leftContinuationPath_factor_of_length_le
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y)
    (p q : P.LeftContinuationPath a)
    (h : p.1.2.length ≤ q.1.2.length) :
    ∃ r : Quiver.Path q.1.1 p.1.1,
      q.1.2 = r.comp p.1.2 := by
  obtain ⟨v, r, s, hq, hr⟩ :=
    q.1.2.exists_eq_comp_of_le_length
      (show q.1.2.length - p.1.2.length ≤ q.1.2.length by omega)
  have hs : s.length = p.1.2.length := by
    have hlen := congrArg Quiver.Path.length hq
    simp only [Quiver.Path.length_comp, hr] at hlen
    omega
  have hs0 :
      arrowMap P.toPresentation.relations a ≫
          pathMap P.toPresentation.relations s ≠ 0 := by
    intro hzero
    apply q.2
    rw [hq, ← pathMap_comp, ← Category.assoc, hzero,
      CategoryTheory.Limits.zero_comp]
  let ps : P.LeftContinuationPathAtLength a p.1.2.length :=
    ⟨p.1, rfl, p.2⟩
  let qs : P.LeftContinuationPathAtLength a p.1.2.length :=
    ⟨⟨v, s⟩, hs, hs0⟩
  have hpq : ps = qs :=
    @Subsingleton.elim _
      (P.leftContinuationPathAtLength_subsingleton p.1.2.length a) ps qs
  have hbase : p.1 = (⟨v, s⟩ : Σ z : Q, Quiver.Path z x) :=
    congrArg
      (fun t : P.LeftContinuationPathAtLength a p.1.2.length ↦ t.1) hpq
  have hv : p.1.1 = v := (Sigma.ext_iff.mp hbase).1
  have hps : p.1.2 ≍ s := (Sigma.ext_iff.mp hbase).2
  subst v
  have hpath : p.1.2 = s := eq_of_heq hps
  subst s
  exact ⟨r, hq⟩

/-- Under a strict length inequality, the initial factor between two left
continuations has positive length. -/
theorem leftContinuationPath_factor_of_length_lt
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y)
    (p q : P.LeftContinuationPath a)
    (h : p.1.2.length < q.1.2.length) :
    ∃ r : Quiver.Path q.1.1 p.1.1,
      q.1.2 = r.comp p.1.2 ∧ r.length ≠ 0 := by
  obtain ⟨r, hr⟩ :=
    P.leftContinuationPath_factor_of_length_le a p q h.le
  refine ⟨r, hr, ?_⟩
  intro hr0
  have hlen := congrArg Quiver.Path.length hr
  simp only [Quiver.Path.length_comp, hr0, zero_add] at hlen
  omega

/-- Surviving left continuations of `a` with one fixed starting vertex. -/
abbrev LeftContinuationAt
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q) :=
  {p : Quiver.Path z x //
    arrowMap P.toPresentation.relations a ≫
        pathMap P.toPresentation.relations p ≠ 0}

/-- A fixed-start continuation is in particular a continuation with varying
starting vertex. -/
def leftContinuationAtToPath
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q) :
    P.LeftContinuationAt a z → P.LeftContinuationPath a :=
  fun p ↦ ⟨⟨z, p.1⟩, p.2⟩

/-- Forgetting that the starting vertex was fixed is injective. -/
theorem leftContinuationAtToPath_injective
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q) :
    Function.Injective (P.leftContinuationAtToPath a z) := by
  intro p q hpq
  apply Subtype.ext
  have hval := congrArg
    (fun t : P.LeftContinuationPath a ↦ t.1) hpq
  injection hval

/-- Fixed-start continuations form a finite type. -/
theorem leftContinuationAt_finite
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q) :
    Finite (P.LeftContinuationAt a z) := by
  letI : Finite (P.LeftContinuationPath a) :=
    P.leftContinuationPath_finite a
  exact Finite.of_injective (P.leftContinuationAtToPath a z)
    (P.leftContinuationAtToPath_injective a z)

/-- Path length embeds the fixed-start continuation chain into the natural
numbers. -/
def leftContinuationAtLengthEmbedding
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q) :
    P.LeftContinuationAt a z ↪ ℕ :=
  (⟨P.leftContinuationAtToPath a z,
      P.leftContinuationAtToPath_injective a z⟩ :
    P.LeftContinuationAt a z ↪ P.LeftContinuationPath a).trans
    (P.leftContinuationLengthEmbedding a)

/-- At a fixed starting vertex, every longer left continuation is obtained
from every shorter one by adjoining a loop at that vertex. -/
theorem leftContinuationAt_factor_of_length_le
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q)
    (p q : P.LeftContinuationAt a z)
    (h : p.1.length ≤ q.1.length) :
    ∃ r : Quiver.Path z z, q.1 = r.comp p.1 := by
  simpa only [leftContinuationAtToPath] using
    P.leftContinuationPath_factor_of_length_le a
      (P.leftContinuationAtToPath a z p)
      (P.leftContinuationAtToPath a z q) h

/-- A strict increase in left-continuation length gives a positive-length
loop factor at the common starting vertex. -/
theorem leftContinuationAt_factor_of_length_lt
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q)
    (p q : P.LeftContinuationAt a z)
    (h : p.1.length < q.1.length) :
    ∃ r : Quiver.Path z z,
      q.1 = r.comp p.1 ∧ r.length ≠ 0 := by
  obtain ⟨r, hr⟩ := P.leftContinuationAt_factor_of_length_le a z p q h.le
  refine ⟨r, hr, ?_⟩
  intro hrzero
  have hlength := congrArg Quiver.Path.length hr
  simp only [Quiver.Path.length_comp, hrzero, zero_add] at hlength
  omega

end SpecialBiserialPresentation

end MagnitudeConjecture.BoundQuiver
