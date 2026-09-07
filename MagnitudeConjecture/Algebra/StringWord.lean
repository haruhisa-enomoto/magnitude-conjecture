import MagnitudeConjecture.Algebra.StringBoundQuiver
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Combinatorics.Quiver.Symmetric

/-!
# Words for string algebras

A string word is a path in the symmetrified displayed quiver.  Reduction is
expressed by excluding a contiguous arrow--inverse pair.  The monomial
relations are excluded in both orientations: every contiguous positive path
in the word and in its reverse must survive the quotient.

This is the word convention used by Butler--Ringel, phrased without choosing
sign functions at the vertices.  The sign functions are useful for ordering
strings, but are not part of the underlying string or its module.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord

/-- A path in the quiver obtained by adjoining a formal inverse to every
displayed arrow. -/
abbrev SignedPath (x y : Q) :=
  Quiver.Path (show Quiver.Symmetrify Q from x)
    (show Quiver.Symmetrify Q from y)

/-- One arrow in the symmetrified displayed quiver. -/
abbrev SignedArrow (x y : Q) :=
  @Quiver.Hom (Quiver.Symmetrify Q) (Quiver.symmetrifyQuiver Q) x y

/-- Two decompositions of a quiver path at the same length have the same
intermediate vertex, prefix, and suffix. -/
theorem path_comp_decomposition_unique
    {V : Type*} [Quiver V] {a b c d : V}
    {p₁ : Quiver.Path a b} {q₁ : Quiver.Path b d}
    {p₂ : Quiver.Path a c} {q₂ : Quiver.Path c d}
    (hcomp : p₁.comp q₁ = p₂.comp q₂)
    (hlength : p₁.length = p₂.length) :
    ∃ _hbc : b = c, HEq p₁ p₂ ∧ HEq q₁ q₂ := by
  induction q₁ generalizing c p₂ with
  | nil =>
      have hq₂zero : q₂.length = 0 := by
        have htotal := congrArg Quiver.Path.length hcomp
        simp only [Quiver.Path.comp_nil, Quiver.Path.length_comp,
          hlength] at htotal
        omega
      cases q₂ with
      | nil =>
          exact ⟨rfl, heq_of_eq hcomp, HEq.rfl⟩
      | cons q₂ e => simp at hq₂zero
  | @cons e f q₁ arrow ih =>
      cases q₂ with
      | nil =>
          simp only [Quiver.Path.comp_cons, Quiver.Path.comp_nil] at hcomp
          have htotal : p₁.length + q₁.length + 1 = p₂.length := by
            simpa only [Quiver.Path.length_cons, Quiver.Path.length_comp] using
              congrArg Quiver.Path.length hcomp
          rw [hlength] at htotal
          omega
      | cons q₂ arrow' =>
          simp only [Quiver.Path.comp_cons] at hcomp
          have hmiddle := Quiver.Path.obj_eq_of_cons_eq_cons hcomp
          subst hmiddle
          have hprefix : p₁.comp q₁ = p₂.comp q₂ := by
            exact (Quiver.Path.heq_of_cons_eq_cons hcomp).eq
          have harrow : arrow = arrow' := by
            exact (Quiver.Path.hom_heq_of_cons_eq_cons hcomp).eq
          subst arrow'
          rcases ih hprefix hlength with ⟨hbc, hp, hq⟩
          cases hbc
          have hqeq : q₁ = q₂ := hq.eq
          subst q₂
          exact ⟨rfl, hp, HEq.rfl⟩

/-- If two paths are prefixes of the same path, the shorter one is a prefix
of the longer one. -/
theorem path_exists_comp_of_comp_eq_comp_of_length_le
    {V : Type*} [Quiver V] {a b c d : V}
    {p₁ : Quiver.Path a b} {q₁ : Quiver.Path b d}
    {p₂ : Quiver.Path a c} {q₂ : Quiver.Path c d}
    (hcomp : p₁.comp q₁ = p₂.comp q₂)
    (hlength : p₁.length ≤ p₂.length) :
    ∃ t : Quiver.Path b c, p₂ = p₁.comp t := by
  rcases p₂.exists_eq_comp_of_le_length hlength with
    ⟨v, pref, suffix, hp₂, hprefLength⟩
  have htotal : p₁.comp q₁ =
      pref.comp (suffix.comp q₂) := by
    rw [← Quiver.Path.comp_assoc, ← hp₂]
    exact hcomp
  rcases path_comp_decomposition_unique htotal hprefLength.symm with
    ⟨h, hp, _⟩
  cases h
  have hpEq : p₁ = pref := hp.eq
  subst pref
  exact ⟨suffix, hp₂⟩

/-- A path occurs contiguously inside another path when the latter factors as
a prefix, followed by that path, followed by a suffix. -/
def IsContiguousSubpath {V : Type*} [Quiver V]
    {x y a b : V} (p : Quiver.Path x y) (w : Quiver.Path a b) : Prop :=
  ∃ (l : Quiver.Path a x) (r : Quiver.Path y b),
    w = l.comp (p.comp r)

/-- Every path is a contiguous subpath of itself. -/
theorem isContiguousSubpath_refl {V : Type*} [Quiver V]
    {x y : V} (p : Quiver.Path x y) : IsContiguousSubpath p p := by
  exact ⟨Quiver.Path.nil, Quiver.Path.nil, by simp⟩

/-- Contiguous-subpath containment is transitive. -/
theorem IsContiguousSubpath.trans {V : Type*} [Quiver V]
    {x y a b c d : V}
    {p : Quiver.Path x y} {q : Quiver.Path a b}
    {w : Quiver.Path c d}
    (hpq : IsContiguousSubpath p q)
    (hqw : IsContiguousSubpath q w) :
    IsContiguousSubpath p w := by
  rcases hpq with ⟨l₁, r₁, rfl⟩
  rcases hqw with ⟨l₂, r₂, rfl⟩
  refine ⟨l₂.comp l₁, r₁.comp r₂, ?_⟩
  simp only [Quiver.Path.comp_assoc]

/-- A contiguous subpath cannot be longer than the ambient path. -/
theorem IsContiguousSubpath.length_le {V : Type*} [Quiver V]
    {x y a b : V} {p : Quiver.Path x y} {w : Quiver.Path a b}
    (h : IsContiguousSubpath p w) : p.length ≤ w.length := by
  rcases h with ⟨l, r, rfl⟩
  simp only [Quiver.Path.length_comp]
  omega

/-- If a contiguous subpath of `left ++ e ++ right` does not contain the
distinguished boundary arrow `e`, then it lies wholly on one side of that
boundary. -/
theorem isContiguousSubpath_comp_toPath_comp_of_not_boundary
    {a b c d x y : Q}
    {p : SignedPath x y}
    (left : SignedPath a b) (e : SignedArrow b c)
    (right : SignedPath c d)
    (hsub : IsContiguousSubpath p
      (left.comp (e.toPath.comp right)))
    (hboundary : ¬ IsContiguousSubpath e.toPath p) :
    IsContiguousSubpath p left ∨ IsContiguousSubpath p right := by
  rcases hsub with ⟨before, after, htotal⟩
  by_cases hleft : before.length + p.length ≤ left.length
  · left
    have hprefix :
        (before.comp p).comp after =
          left.comp (e.toPath.comp right) := by
      rw [Quiver.Path.comp_assoc, ← htotal]
    rcases path_exists_comp_of_comp_eq_comp_of_length_le
        hprefix (by
          simp only [Quiver.Path.length_comp]
          exact hleft) with ⟨tail, hleftFactor⟩
    refine ⟨before, tail, ?_⟩
    rw [hleftFactor, Quiver.Path.comp_assoc]
  · by_cases hright : left.length + 1 ≤ before.length
    · right
      have hprefix :
          (left.comp e.toPath).comp right =
            before.comp (p.comp after) := by
        simpa only [Quiver.Path.comp_assoc] using htotal
      rcases path_exists_comp_of_comp_eq_comp_of_length_le
          hprefix (by
            simp only [Quiver.Path.length_comp,
              Quiver.Path.length_toPath]
            exact hright) with ⟨middle, hbeforeFactor⟩
      have hcancel : right = middle.comp (p.comp after) := by
        apply Quiver.Path.comp_injective_right (left.comp e.toPath)
        simpa only [Quiver.Path.comp_assoc, hbeforeFactor] using hprefix
      exact ⟨middle, after, hcancel⟩
    · exfalso
      apply hboundary
      have hbeforeLe : before.length ≤ left.length := by omega
      have hprefix :
          before.comp (p.comp after) =
            left.comp (e.toPath.comp right) := htotal.symm
      rcases path_exists_comp_of_comp_eq_comp_of_length_le
          hprefix hbeforeLe with ⟨middle, hleftFactor⟩
      have hmiddleLength :
          left.length = before.length + middle.length := by
        rw [hleftFactor, Quiver.Path.length_comp]
      have hcancelBefore :
          p.comp after = middle.comp (e.toPath.comp right) := by
        apply Quiver.Path.comp_injective_right before
        simpa only [Quiver.Path.comp_assoc, hleftFactor] using hprefix
      have hmiddleLt : middle.length < p.length := by omega
      rcases path_exists_comp_of_comp_eq_comp_of_length_le
          hcancelBefore.symm (Nat.le_of_lt hmiddleLt) with
        ⟨remaining, hpFactor⟩
      have hremainingPos : 0 < remaining.length := by
        have hpLength := congrArg Quiver.Path.length hpFactor
        simp only [Quiver.Path.length_comp] at hpLength
        omega
      have hcancelMiddle :
          remaining.comp after = e.toPath.comp right := by
        apply Quiver.Path.comp_injective_right middle
        simpa only [Quiver.Path.comp_assoc, hpFactor] using hcancelBefore
      rcases path_exists_comp_of_comp_eq_comp_of_length_le
          hcancelMiddle.symm (by
            simp only [Quiver.Path.length_toPath]
            exact hremainingPos) with ⟨tail, hremainingFactor⟩
      refine ⟨middle, tail, ?_⟩
      calc
        p = middle.comp remaining := hpFactor
        _ = middle.comp (e.toPath.comp tail) := by rw [hremainingFactor]

/-- A contiguous subpath short enough not to span a nonempty overlap lies in
one of the two overlapping paths. -/
theorem isContiguousSubpath_comp_overlap
    {a b c d x y : Q}
    {p : SignedPath x y}
    (left : SignedPath a b) (middle : SignedPath b c)
    (right : SignedPath c d)
    (hsub : IsContiguousSubpath p
      (left.comp (middle.comp right)))
    (hlength : p.length ≤ middle.length + 1) :
    IsContiguousSubpath p (left.comp middle) ∨
      IsContiguousSubpath p (middle.comp right) := by
  rcases hsub with ⟨before, after, htotal⟩
  by_cases hleft : before.length + p.length ≤
      (left.comp middle).length
  · left
    have hprefix :
        (before.comp p).comp after =
          (left.comp middle).comp right := by
      simpa only [Quiver.Path.comp_assoc] using htotal.symm
    rcases path_exists_comp_of_comp_eq_comp_of_length_le
        hprefix (by
          simp only [Quiver.Path.length_comp]
          simpa only [Quiver.Path.length_comp] using hleft) with
      ⟨tail, hfactor⟩
    exact ⟨before, tail, by
      rw [hfactor, Quiver.Path.comp_assoc]⟩
  · right
    have hstart : left.length ≤ before.length := by
      simp only [Quiver.Path.length_comp] at hleft
      by_contra hnot
      have hbeforeLt : before.length < left.length :=
        Nat.lt_of_not_ge hnot
      omega
    have hprefix :
        left.comp (middle.comp right) =
          before.comp (p.comp after) := htotal
    rcases path_exists_comp_of_comp_eq_comp_of_length_le
        hprefix hstart with ⟨initial, hbeforeFactor⟩
    have hcancel :
        middle.comp right = initial.comp (p.comp after) := by
      apply Quiver.Path.comp_injective_right left
      simpa only [Quiver.Path.comp_assoc, hbeforeFactor] using hprefix
    exact ⟨initial, after, hcancel⟩

/-- Reversal carries a contiguous subpath to the reversed contiguous
subpath, and conversely. -/
theorem isContiguousSubpath_reverse_iff
    {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {x y a b : V} (p : Quiver.Path x y) (w : Quiver.Path a b) :
    IsContiguousSubpath p.reverse w.reverse ↔
      IsContiguousSubpath p w := by
  constructor
  · rintro ⟨l, r, h⟩
    refine ⟨r.reverse, l.reverse, ?_⟩
    have h' := congrArg Quiver.Path.reverse h
    simpa only [Quiver.Path.reverse_reverse, Quiver.Path.reverse_comp,
      Quiver.Path.comp_assoc] using h'
  · rintro ⟨l, r, h⟩
    refine ⟨r.reverse, l.reverse, ?_⟩
    simpa only [Quiver.Path.reverse_comp, Quiver.Path.comp_assoc] using
      congrArg Quiver.Path.reverse h

/-- Reversing a path preserves its length. -/
theorem length_reverse {V : Type*} [Quiver V] [Quiver.HasReverse V]
    {x y : V} (p : Quiver.Path x y) : p.reverse.length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih, Nat.add_comm]

/-- The positive signed copy of a displayed arrow, with the symmetrified
quiver instance pinned explicitly. -/
def positiveArrow {x y : Q} (a : x ⟶ y) :
    SignedArrow x y :=
  Sum.inl a

/-- The negative signed copy of a displayed arrow, traversed backwards. -/
def negativeArrow {x y : Q} (a : x ⟶ y) :
    SignedArrow y x :=
  Sum.inr a

@[simp]
theorem reverse_positiveArrow {x y : Q} (a : x ⟶ y) :
    Quiver.reverse (positiveArrow a) = negativeArrow a := rfl

@[simp]
theorem reverse_negativeArrow {x y : Q} (a : x ⟶ y) :
    Quiver.reverse (negativeArrow a) = positiveArrow a := rfl

/-- The positive copy of an ordinary displayed-quiver path in the
symmetrified quiver. -/
def positivePath {x y : Q} (p : Quiver.Path x y) :
    SignedPath x y :=
  (Quiver.Symmetrify.of (V := Q)).mapPath p

@[simp]
theorem positivePath_nil (x : Q) :
    positivePath (Q := Q) (Quiver.Path.nil : Quiver.Path x x) =
      Quiver.Path.nil := by
  rfl

@[simp]
theorem positivePath_comp {x y z : Q}
    (p : Quiver.Path x y) (q : Quiver.Path y z) :
    positivePath (p.comp q) = (positivePath p).comp (positivePath q) := by
  exact (Quiver.Symmetrify.of (V := Q)).mapPath_comp p q

@[simp]
theorem positivePath_cons {x y z : Q}
    (p : Quiver.Path x y) (a : y ⟶ z) :
    positivePath (p.cons a) =
      (positivePath p).comp (positivePath a.toPath) := by
  exact positivePath_comp p a.toPath

@[simp]
theorem positivePath_length {x y : Q} (p : Quiver.Path x y) :
    (positivePath (Q := Q) p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change (positivePath p).length + 1 = p.length + 1
      rw [ih]

@[simp]
theorem positivePath_toPath {x y : Q} (a : x ⟶ y) :
    positivePath (Q := Q) a.toPath = (positiveArrow a).toPath := by
  exact (Quiver.Symmetrify.of (V := Q)).mapPath_toPath a

/-- The signs of a signed path, listed from its final letter backwards. -/
def signedPathSigns {x : Quiver.Symmetrify Q} :
    ∀ {y : Quiver.Symmetrify Q}, Quiver.Path x y → List Bool
  | _, Quiver.Path.nil => []
  | _, Quiver.Path.cons p e =>
      (match e with
        | Sum.inl _ => false
        | Sum.inr _ => true) :: signedPathSigns p

@[simp]
theorem signedPathSigns_comp
    {x y z : Quiver.Symmetrify Q}
    (p : Quiver.Path x y) (q : Quiver.Path y z) :
    signedPathSigns (p.comp q) =
      signedPathSigns q ++ signedPathSigns p := by
  induction q with
  | nil => simp [signedPathSigns]
  | cons q e ih =>
      cases e <;> simp [signedPathSigns, ih]

@[simp]
theorem signedPathSigns_positivePath {x y : Q}
    (p : Quiver.Path x y) :
    signedPathSigns (positivePath p) =
      List.replicate p.length false := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [positivePath_cons, signedPathSigns_comp, ih]
      rfl

@[simp]
theorem signedPathSigns_negativeArrow {x y : Q} (a : x ⟶ y) :
    signedPathSigns (negativeArrow a).toPath = [true] :=
  rfl

/-- A negative signed arrow cannot occur inside a positive ordinary path. -/
theorem not_negativeArrow_contiguousSubpath_positivePath
    {x y a b : Q} (e : x ⟶ y) (p : Quiver.Path a b) :
    ¬ IsContiguousSubpath (negativeArrow e).toPath
      (positivePath p) := by
  rintro ⟨left, right, hfactor⟩
  have hsigns := congrArg signedPathSigns hfactor
  simp only [signedPathSigns_comp, signedPathSigns_positivePath,
    signedPathSigns_negativeArrow] at hsigns
  have hmem : true ∈ List.replicate p.length false := by
    rw [hsigns]
    simp
  simp at hmem

/-- A signed path is reduced when it contains no adjacent formal inverse
pair. -/
def IsReduced {x y : Q}
    (w : SignedPath x y) : Prop :=
  ∀ {a b : Q}
      (e : SignedArrow a b),
    ¬ IsContiguousSubpath
      (e.toPath.comp (Quiver.reverse e).toPath) w

/-- Reduction is invariant under reversing a signed path. -/
theorem isReduced_reverse_iff {x y : Q}
    (w : SignedPath x y) :
    IsReduced w.reverse ↔ IsReduced w := by
  constructor
  · intro h a b e he
    apply h e
    have hsub :=
      (isContiguousSubpath_reverse_iff
        (e.toPath.comp (Quiver.reverse e).toPath) w).2 he
    simpa using hsub
  · intro h a b e he
    apply h e
    have he' : IsContiguousSubpath
        (e.toPath.comp (Quiver.reverse e).toPath).reverse w.reverse := by
      simpa using he
    exact (isContiguousSubpath_reverse_iff
      (e.toPath.comp (Quiver.reverse e).toPath) w).1 he'

/-- Every signed path of length at most one is reduced. -/
theorem isReduced_of_length_lt_two {x y : Q}
    (w : SignedPath x y) (hw : w.length < 2) : IsReduced w := by
  intro a b e hsub
  have hle := hsub.length_le
  simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hle
  omega

/-- A two-letter signed path is reduced when its second letter is not the
formal inverse of its first, allowing the endpoints to be dependent. -/
theorem isReduced_toPath_comp_toPath_of_not_heq_reverse
    {a b c : Q} (e : SignedArrow a b) (f : SignedArrow b c)
    (hnot : ¬ HEq f (Quiver.reverse e)) :
    IsReduced (e.toPath.comp f.toPath) := by
  intro x y g hsub
  rcases hsub with ⟨before, after, hword⟩
  have hlength := congrArg Quiver.Path.length hword
  simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
  have hbeforeZero : before.length = 0 := by omega
  have hafterZero : after.length = 0 := by omega
  have hsource := before.eq_of_length_zero hbeforeZero
  have htarget := after.eq_of_length_zero hafterZero
  cases hsource
  cases htarget
  have hbeforeNil := before.eq_nil_of_length_zero hbeforeZero
  have hafterNil := after.eq_nil_of_length_zero hafterZero
  subst before
  subst after
  simp only [Quiver.Path.nil_comp, Quiver.Path.comp_nil,
    Quiver.Path.comp_toPath_eq_cons] at hword
  have hmiddle := Quiver.Path.obj_eq_of_cons_eq_cons hword
  cases hmiddle
  have hprefix : e.toPath = g.toPath :=
    (Quiver.Path.heq_of_cons_eq_cons hword).eq
  change (Quiver.Path.nil.cons e) = (Quiver.Path.nil.cons g) at hprefix
  have he : e = g :=
    (Quiver.Path.hom_heq_of_cons_eq_cons hprefix).eq
  subst g
  exact hnot (Quiver.Path.hom_heq_of_cons_eq_cons hword)

/-- A zero-length path between two noncancelling signed letters does not
affect reducedness. -/
theorem isReduced_toPath_comp_zero_comp_toPath_of_not_heq_reverse
    {a b c d : Q} (e : SignedArrow a b) (middle : SignedPath b c)
    (f : SignedArrow c d) (hmiddle : middle.length = 0)
    (hnot : ¬ HEq f (Quiver.reverse e)) :
    IsReduced (e.toPath.comp (middle.comp f.toPath)) := by
  have hbc := middle.eq_of_length_zero hmiddle
  change b = c at hbc
  subst c
  have hmiddleNil := middle.eq_nil_of_length_zero hmiddle
  subst middle
  change IsReduced (e.toPath.comp f.toPath)
  exact isReduced_toPath_comp_toPath_of_not_heq_reverse e f hnot

/-- Every contiguous subpath of a reduced signed path is reduced. -/
theorem IsReduced.of_contiguousSubpath {x y a b : Q}
    {p : SignedPath x y} {w : SignedPath a b}
    (hw : IsReduced w) (hpw : IsContiguousSubpath p w) :
    IsReduced p := by
  intro c d e hep
  exact hw e (hep.trans hpw)

/-- Reducedness glues across a nonempty overlap: an inverse pair is too
short to span both ends of that overlap. -/
theorem isReduced_comp_of_overlap
    {a b c d : Q}
    (left : SignedPath a b) (middle : SignedPath b c)
    (right : SignedPath c d)
    (hmiddle : 0 < middle.length)
    (hleft : IsReduced (left.comp middle))
    (hright : IsReduced (middle.comp right)) :
    IsReduced (left.comp (middle.comp right)) := by
  intro x y e hsub
  rcases isContiguousSubpath_comp_overlap left middle right hsub
      (by
        simp only [Quiver.Path.length_comp,
          Quiver.Path.length_toPath]
        omega) with hsubLeft | hsubRight
  · exact hleft e hsubLeft
  · exact hright e hsubRight

variable (R : RelationFamily k Q)

/-- Every positive ordinary-quiver path occurring in the signed word
survives the relation quotient. -/
def AvoidsRelations {x y : Q}
    (w : SignedPath x y) : Prop :=
  ∀ {a b : Q} (p : Quiver.Path a b),
    IsContiguousSubpath (positivePath p) w → pathMap R p ≠ 0

/-- In an admissible quotient, every signed word of length at most one avoids
relations: all of its positive subpaths have length below two. -/
theorem avoidsRelations_of_length_lt_two
    (hR : IsAdmissible R) {x y : Q}
    (w : SignedPath x y) (hw : w.length < 2) : AvoidsRelations R w := by
  intro a b p hsub
  apply pathMap_ne_zero_of_length_lt_two hR p
  exact lt_of_le_of_lt (by simpa using hsub.length_le) hw

/-- Avoiding the monomial relations is inherited by contiguous subpaths. -/
theorem AvoidsRelations.of_contiguousSubpath {x y a b : Q}
    {p : SignedPath x y} {w : SignedPath a b}
    (hw : AvoidsRelations R w) (hpw : IsContiguousSubpath p w) :
    AvoidsRelations R p := by
  intro c d q hqp
  exact hw q (hqp.trans hpw)

/-- A negative signed boundary blocks every positive ordinary subpath, so
avoidance of relations glues across it. -/
theorem avoidsRelations_comp_negativeArrow_comp
    {a b d : Q}
    (left : SignedPath a b) {x : Q} (e : x ⟶ b)
    (right : SignedPath x d)
    (hleft : AvoidsRelations R left)
    (hright : AvoidsRelations R right) :
    AvoidsRelations R
      (left.comp ((negativeArrow e).toPath.comp right)) := by
  intro u v p hsub
  rcases isContiguousSubpath_comp_toPath_comp_of_not_boundary
      left (negativeArrow e) right hsub
      (not_negativeArrow_contiguousSubpath_positivePath e p) with
    hleftSub | hrightSub
  · exact hleft p hleftSub
  · exact hright p hrightSub

/-- The Butler--Ringel string condition: the signed path is reduced and no
positive subpath of it or of its inverse belongs to the monomial relation
ideal. -/
def IsString {x y : Q}
    (w : SignedPath x y) : Prop :=
  IsReduced w ∧ AvoidsRelations R w ∧ AvoidsRelations R w.reverse

/-- Casting the displayed endpoints of a signed path does not change whether
it is a string. -/
theorem isString_cast
    {a b a' b' : Quiver.Symmetrify Q}
    (ha : a = a') (hb : b = b') (p : Quiver.Path a b) :
    IsString R (@Quiver.Path.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) a b a' b' ha hb p) ↔
      IsString R p := by
  subst a'
  subst b'
  rfl

/-- Casting the endpoint of a prefix and casting the source of the appended
arrow cancel when the two pieces are composed. -/
theorem path_cast_comp_cast_toPath
    {a b a' b' c : Quiver.Symmetrify Q}
    (p : Quiver.Path a b) (e : b' ⟶ c)
    (ha : a = a') (hb : b = b') :
    (@Quiver.Path.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) a c a' c ha rfl
      (p.comp
        (@Quiver.Hom.cast (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) b' c b c hb.symm rfl e).toPath)) =
      (@Quiver.Path.cast (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) a b a' b' ha hb p).comp e.toPath := by
  subst a'
  subst b'
  rfl

/-- Casting only the target of a quiver path is injective. -/
theorem path_cast_target_injective
    {V : Type*} [Quiver V] {a b b' : V} (h : b = b') :
    Function.Injective
      (fun p : Quiver.Path a b ↦
        @Quiver.Path.cast V _ a b a b' rfl h p) := by
  subst b'
  exact Function.injective_id

/-- Endpoint casts preserve path length. -/
@[simp]
theorem path_cast_length
    {V : Type*} [Quiver V] {a b a' b' : V}
    (ha : a = a') (hb : b = b') (p : Quiver.Path a b) :
    (@Quiver.Path.cast V _ a b a' b' ha hb p).length = p.length := by
  subst a'
  subst b'
  rfl

/-- Casting the target of a composite is the same as casting the target of
its second factor. -/
theorem path_cast_comp_target
    {V : Type*} [Quiver V] {a b c c' : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) (h : c = c') :
    (@Quiver.Path.cast V _ a c a c' rfl h (p.comp q)) =
      p.comp (@Quiver.Path.cast V _ b c b c' rfl h q) := by
  subst c'
  rfl

/-- Reversing an endpoint-cast path casts the reversed path at the swapped
endpoints. -/
theorem path_reverse_cast
    {a b a' b' : Quiver.Symmetrify Q}
    (ha : a = a') (hb : b = b') (p : Quiver.Path a b) :
    (@Quiver.Path.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) a b a' b' ha hb p).reverse =
      @Quiver.Path.cast (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) b a b' a' hb ha p.reverse := by
  subst a'
  subst b'
  rfl

/-- A string extension may be transported across endpoint equalities by
casting the old path and the new arrow in opposite directions. -/
theorem isString_comp_cast_toPath
    {a b a' b' c : Quiver.Symmetrify Q}
    (p : Quiver.Path a b) (e : b' ⟶ c)
    (ha : a = a') (hb : b = b')
    (h : IsString R
      ((@Quiver.Path.cast (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) a b a' b' ha hb p).comp e.toPath)) :
    IsString R
      (p.comp
        (@Quiver.Hom.cast (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) b' c b c hb.symm rfl e).toPath) := by
  rw [← isString_cast R ha rfl]
  rwa [path_cast_comp_cast_toPath]

/-- Once reducedness is known, two one-ended strings glue across a negative
left boundary and a positive right boundary.  The signs prevent relations
from crossing either seam. -/
theorem isString_comp_of_negative_positive_boundaries_of_reduced
    {a b c d e f : Q}
    (leftTail : SignedPath a b) (leftArrow : c ⟶ b)
    (middle : SignedPath c d) (rightArrow : d ⟶ e)
    (rightTail : SignedPath e f)
    (hreduced : IsReduced
      (leftTail.comp ((negativeArrow leftArrow).toPath.comp
        (middle.comp ((positiveArrow rightArrow).toPath.comp rightTail)))))
    (hleft : IsString R
      (leftTail.comp ((negativeArrow leftArrow).toPath.comp middle)))
    (hright : IsString R
      (middle.comp ((positiveArrow rightArrow).toPath.comp rightTail))) :
    IsString R
      (leftTail.comp ((negativeArrow leftArrow).toPath.comp
        (middle.comp ((positiveArrow rightArrow).toPath.comp rightTail)))) := by
  have hleftTail : AvoidsRelations R leftTail := by
    apply AvoidsRelations.of_contiguousSubpath R hleft.2.1
    exact ⟨Quiver.Path.nil,
      (negativeArrow leftArrow).toPath.comp middle, by simp⟩
  have hforward : AvoidsRelations R
      (leftTail.comp ((negativeArrow leftArrow).toPath.comp
        (middle.comp ((positiveArrow rightArrow).toPath.comp
          rightTail)))) :=
    avoidsRelations_comp_negativeArrow_comp R
      (a := a) (b := b) (d := f) (x := c)
      leftTail leftArrow
      (middle.comp ((positiveArrow rightArrow).toPath.comp rightTail))
      hleftTail hright.2.1
  have hrightTailReverse : AvoidsRelations R rightTail.reverse := by
    apply AvoidsRelations.of_contiguousSubpath R hright.2.2
    refine ⟨Quiver.Path.nil,
      (negativeArrow rightArrow).toPath.comp middle.reverse, ?_⟩
    simp only [Quiver.Path.nil_comp, Quiver.Path.reverse_comp,
      Quiver.Path.reverse_toPath, reverse_positiveArrow,
      Quiver.Path.comp_assoc]
  have hreverse : AvoidsRelations R
      (rightTail.reverse.comp ((negativeArrow rightArrow).toPath.comp
        (leftTail.comp ((negativeArrow leftArrow).toPath.comp
          middle)).reverse)) :=
    avoidsRelations_comp_negativeArrow_comp R
      (a := f) (b := e) (d := a) (x := d)
      rightTail.reverse rightArrow
      (leftTail.comp ((negativeArrow leftArrow).toPath.comp middle)).reverse
      hrightTailReverse hleft.2.2
  refine ⟨?_, ?_, ?_⟩
  · exact hreduced
  · intro x y p hsub
    exact hforward p hsub
  · intro x y p hsub
    apply hreverse p
    simpa only [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
      reverse_positiveArrow, Quiver.Path.comp_assoc] using hsub

/-- Two strings with a nonempty common middle glue when the new outer
boundaries have the hook signs: negative on the left and positive on the
right. -/
theorem isString_comp_of_negative_positive_boundaries
    {a b c d e f : Q}
    (leftTail : SignedPath a b) (leftArrow : c ⟶ b)
    (middle : SignedPath c d) (rightArrow : d ⟶ e)
    (rightTail : SignedPath e f)
    (hmiddle : 0 < middle.length)
    (hleft : IsString R
      (leftTail.comp ((negativeArrow leftArrow).toPath.comp middle)))
    (hright : IsString R
      (middle.comp ((positiveArrow rightArrow).toPath.comp rightTail))) :
    IsString R
      (leftTail.comp ((negativeArrow leftArrow).toPath.comp
        (middle.comp ((positiveArrow rightArrow).toPath.comp rightTail)))) := by
  let leftBoundary : SignedPath a c :=
    leftTail.comp (negativeArrow leftArrow).toPath
  let rightBoundary : SignedPath d f :=
    (positiveArrow rightArrow).toPath.comp rightTail
  have hreduced : IsReduced
      (leftBoundary.comp (middle.comp rightBoundary)) := by
    apply isReduced_comp_of_overlap leftBoundary middle rightBoundary hmiddle
    · intro x y signedArrow hsub
      apply hleft.1 signedArrow
      simpa only [leftBoundary, Quiver.Path.comp_assoc] using hsub
    · exact hright.1
  apply isString_comp_of_negative_positive_boundaries_of_reduced R
    leftTail leftArrow middle rightArrow rightTail
  · intro x y signedArrow hsub
    apply hreduced signedArrow
    simpa only [leftBoundary, rightBoundary,
      Quiver.Path.comp_assoc] using hsub
  · exact hleft
  · exact hright

/-- Every signed path of length at most one is a string for an admissible
bound-quiver presentation. -/
theorem isString_of_length_lt_two
    (hR : IsAdmissible R) {x y : Q}
    (w : SignedPath x y) (hw : w.length < 2) : IsString R w := by
  refine ⟨isReduced_of_length_lt_two w hw,
    avoidsRelations_of_length_lt_two R hR w hw, ?_⟩
  apply avoidsRelations_of_length_lt_two R hR w.reverse
  rwa [length_reverse]

/-- A string remains a string after reversing every letter and the order of
the word. -/
theorem isString_reverse_iff {x y : Q}
    (w : SignedPath x y) :
    IsString R w.reverse ↔ IsString R w := by
  constructor
  · rintro ⟨hred, hforward, hreverse⟩
    refine ⟨(isReduced_reverse_iff w).1 hred, ?_, hforward⟩
    intro a b p hp
    apply hreverse p
    simpa only [Quiver.Path.reverse_reverse] using hp
  · rintro ⟨hred, hforward, hreverse⟩
    refine ⟨(isReduced_reverse_iff w).2 hred, hreverse, ?_⟩
    intro a b p hp
    apply hforward p
    simpa only [Quiver.Path.reverse_reverse] using hp

/-- Every contiguous subpath of a string is a string. -/
theorem IsString.of_contiguousSubpath {x y a b : Q}
    {p : SignedPath x y} {w : SignedPath a b}
    (hw : IsString R w) (hpw : IsContiguousSubpath p w) :
    IsString R p := by
  rcases hw with ⟨hred, hforward, hreverse⟩
  refine ⟨hred.of_contiguousSubpath hpw,
    AvoidsRelations.of_contiguousSubpath R hforward hpw, ?_⟩
  apply AvoidsRelations.of_contiguousSubpath R hreverse
  exact (isContiguousSubpath_reverse_iff p w).2 hpw

/-- A bundled string word, including its displayed endpoints. -/
structure Word where
  source : Q
  target : Q
  path : SignedPath source target
  isString : IsString R path

namespace Word

/-- Two consecutive positive letters cannot cancel. -/
theorem isReduced_positiveArrow_comp_positiveArrow
    {x y z : Q} (a : x ⟶ y) (b : y ⟶ z) :
    IsReduced ((positiveArrow a).toPath.comp (positiveArrow b).toPath) := by
  intro u v e hsub
  rcases hsub with ⟨before, after, hword⟩
  have hlength := congrArg Quiver.Path.length hword
  simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
  have hbeforeZero : before.length = 0 := by omega
  have hafterZero : after.length = 0 := by omega
  have hsource := before.eq_of_length_zero hbeforeZero
  have htarget := after.eq_of_length_zero hafterZero
  cases hsource
  cases htarget
  have hbeforeNil := before.eq_nil_of_length_zero hbeforeZero
  have hafterNil := after.eq_nil_of_length_zero hafterZero
  subst before
  subst after
  have hsigns := congrArg signedPathSigns hword
  cases e with
  | inl _ =>
      simp [signedPathSigns, Quiver.symmetrify_reverse,
        positiveArrow] at hsigns
  | inr _ =>
      simp [signedPathSigns, Quiver.symmetrify_reverse,
        positiveArrow] at hsigns
      change [false] = [true] at hsigns
      simp at hsigns

/-- Two consecutive negative letters cannot cancel. -/
theorem isReduced_negativeArrow_comp_negativeArrow
    {x y z : Q} (a : y ⟶ x) (b : z ⟶ y) :
    IsReduced ((negativeArrow a).toPath.comp (negativeArrow b).toPath) := by
  intro u v e hsub
  rcases hsub with ⟨before, after, hword⟩
  have hlength := congrArg Quiver.Path.length hword
  simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
  have hbeforeZero : before.length = 0 := by omega
  have hafterZero : after.length = 0 := by omega
  have hsource := before.eq_of_length_zero hbeforeZero
  have htarget := after.eq_of_length_zero hafterZero
  cases hsource
  cases htarget
  have hbeforeNil := before.eq_nil_of_length_zero hbeforeZero
  have hafterNil := after.eq_nil_of_length_zero hafterZero
  subst before
  subst after
  have hsigns := congrArg signedPathSigns hword
  cases e with
  | inl _ =>
      simp [signedPathSigns, Quiver.symmetrify_reverse,
        negativeArrow] at hsigns
      change [true] = [false] at hsigns
      simp at hsigns
  | inr _ =>
      simp [signedPathSigns, Quiver.symmetrify_reverse,
        negativeArrow] at hsigns

/-- A negative letter followed by a positive letter is reduced when their
underlying arrows are distinct in the common-source star. -/
theorem isReduced_negativeArrow_comp_positiveArrow_of_star_ne
    {x y z : Q} (b : x ⟶ y) (a : x ⟶ z)
    (hba : (⟨y, b⟩ : Quiver.Star x) ≠ ⟨z, a⟩) :
    IsReduced ((negativeArrow b).toPath.comp (positiveArrow a).toPath) := by
  intro u v e hsub
  rcases hsub with ⟨before, after, hword⟩
  have hlength := congrArg Quiver.Path.length hword
  simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
  have hbeforeZero : before.length = 0 := by omega
  have hafterZero : after.length = 0 := by omega
  have hsource := before.eq_of_length_zero hbeforeZero
  have htarget := after.eq_of_length_zero hafterZero
  cases hsource
  cases htarget
  have hbeforeNil := before.eq_nil_of_length_zero hbeforeZero
  have hafterNil := after.eq_nil_of_length_zero hafterZero
  subst before
  subst after
  simp only [Quiver.Path.nil_comp, Quiver.Path.comp_nil] at hword
  cases e with
  | inl c =>
      have hsigns := congrArg signedPathSigns hword
      simp [signedPathSigns, Quiver.symmetrify_reverse,
        negativeArrow, positiveArrow] at hsigns
  | inr c =>
      have hprefLength : (negativeArrow b).toPath.length =
          (negativeArrow c).toPath.length := by simp
      rcases path_comp_decomposition_unique hword hprefLength with
        ⟨hmiddle, hprefix, hsuffix⟩
      cases hmiddle
      have hprefixArrow :=
        Quiver.Path.hom_heq_of_cons_eq_cons hprefix.eq
      cases hprefixArrow
      have hsuffixArrow :=
        Quiver.Path.hom_heq_of_cons_eq_cons hsuffix.eq
      cases hsuffixArrow
      exact hba rfl

/-- A positive letter followed by a negative letter is reduced when their
underlying arrows are distinct in the common-target costar. -/
theorem isReduced_positiveArrow_comp_negativeArrow_of_costar_ne
    {x y z : Q} (a : x ⟶ y) (b : z ⟶ y)
    (hab : (⟨x, a⟩ : Quiver.Costar y) ≠ ⟨z, b⟩) :
    IsReduced ((positiveArrow a).toPath.comp (negativeArrow b).toPath) := by
  intro u v e hsub
  rcases hsub with ⟨before, after, hword⟩
  have hlength := congrArg Quiver.Path.length hword
  simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
  have hbeforeZero : before.length = 0 := by omega
  have hafterZero : after.length = 0 := by omega
  have hsource := before.eq_of_length_zero hbeforeZero
  have htarget := after.eq_of_length_zero hafterZero
  cases hsource
  cases htarget
  have hbeforeNil := before.eq_nil_of_length_zero hbeforeZero
  have hafterNil := after.eq_nil_of_length_zero hafterZero
  subst before
  subst after
  simp only [Quiver.Path.nil_comp, Quiver.Path.comp_nil] at hword
  cases e with
  | inl c =>
      have hprefLength : (positiveArrow a).toPath.length =
          (positiveArrow c).toPath.length := by simp
      rcases path_comp_decomposition_unique hword hprefLength with
        ⟨hmiddle, hprefix, hsuffix⟩
      cases hmiddle
      have hprefixArrow :=
        Quiver.Path.hom_heq_of_cons_eq_cons hprefix.eq
      cases hprefixArrow
      have hsuffixArrow :=
        Quiver.Path.hom_heq_of_cons_eq_cons hsuffix.eq
      cases hsuffixArrow
      exact hab rfl
  | inr c =>
      have hsigns := congrArg signedPathSigns hword
      simp [signedPathSigns, Quiver.symmetrify_reverse,
        negativeArrow, positiveArrow] at hsigns

/-- Bundled words are equal when their endpoints and dependent paths are
equal; the string proof is proposition-valued. -/
@[ext]
theorem ext {C D : Word R}
    (hsource : C.source = D.source)
    (htarget : C.target = D.target)
    (hpath : HEq C.path D.path) : C = D := by
  rcases C with ⟨source, target, path, hstring⟩
  rcases D with ⟨source', target', path', hstring'⟩
  dsimp at hsource htarget hpath
  subst source'
  subst target'
  simp only [heq_eq_eq] at hpath
  subst path'
  rfl

/-- The length-zero string at a displayed vertex. -/
def vertex (hR : IsAdmissible R) (x : Q) : Word R where
  source := x
  target := x
  path := Quiver.Path.nil
  isString := isString_of_length_lt_two R hR Quiver.Path.nil (by simp)

/-- A displayed arrow as a positive string of length one. -/
def arrow (hR : IsAdmissible R) {x y : Q} (a : x ⟶ y) : Word R where
  source := x
  target := y
  path := positivePath a.toPath
  isString := isString_of_length_lt_two R hR _ (by
    simp only [positivePath_length, Quiver.Path.length_toPath]
    omega)

/-- Reverse a bundled string word. -/
def reverse (C : Word R) : Word R where
  source := C.target
  target := C.source
  path := C.path.reverse
  isString := (isString_reverse_iff R C.path).2 C.isString

/-- A displayed arrow traversed in the inverse direction. -/
def inverseArrow (hR : IsAdmissible R) {x y : Q} (a : x ⟶ y) : Word R :=
  (arrow R hR a).reverse

@[simp]
theorem reverse_source (C : Word R) : C.reverse.source = C.target := rfl

@[simp]
theorem reverse_target (C : Word R) : C.reverse.target = C.source := rfl

@[simp]
theorem reverse_path (C : Word R) : C.reverse.path = C.path.reverse := rfl

@[simp]
theorem reverse_reverse (C : Word R) : C.reverse.reverse = C := by
  apply Word.ext
  · rfl
  · rfl
  · exact heq_of_eq (Quiver.Path.reverse_reverse C.path)

/-- Length of a string word. -/
def length (C : Word R) : ℕ := C.path.length

@[simp]
theorem reverse_length (C : Word R) : C.reverse.length = C.length := by
  exact length_reverse C.path

@[simp]
theorem vertex_length (hR : IsAdmissible R) (x : Q) :
    (vertex R hR x).length = 0 := rfl

@[simp]
theorem arrow_length (hR : IsAdmissible R) {x y : Q} (a : x ⟶ y) :
    (arrow R hR a).length = 1 := by
  rw [length, arrow, positivePath_length]
  rfl

@[simp]
theorem inverseArrow_length (hR : IsAdmissible R)
    {x y : Q} (a : x ⟶ y) :
    (inverseArrow R hR a).length = 1 := by
  rw [inverseArrow, reverse_length, arrow_length]

/-- Append one signed arrow to a string word, provided the extended path is
again a string. -/
def append (C : Word R) {z : Q} (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) : Word R where
  source := C.source
  target := z
  path := C.path.comp e.toPath
  isString := h

@[simp]
theorem append_source (C : Word R) {z : Q} (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) :
    (append R C e h).source = C.source := rfl

@[simp]
theorem append_target (C : Word R) {z : Q} (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) :
    (append R C e h).target = z := rfl

@[simp]
theorem append_path (C : Word R) {z : Q} (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) :
    (append R C e h).path = C.path.comp e.toPath := rfl

@[simp]
theorem append_length (C : Word R) {z : Q} (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) :
    (append R C e h).length = C.length + 1 := by
  simp [length, append]

end Word

end StringWord

end MagnitudeConjecture.BoundQuiver
