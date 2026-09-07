import MagnitudeConjecture.Algebra.StringWord
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# A reduced signed path is not a nontrivial reverse palindrome

We forget the vertices of a signed path but retain each displayed arrow and
its orientation.  This gives a word in a free group.  String reducedness is
exactly enough to make this free-group word reduced, while formal path
reversal becomes inverse-word reversal.  Torsion-freeness of free groups then
excludes a positive-length reduced path equal to its own reverse.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- A displayed-quiver arrow with its two endpoints retained. -/
def SignedGenerator (Q : Type u) [Quiver.{u} Q] :=
  Σ x y : Q, x ⟶ y

/-- Forget the signed endpoints of a symmetrified arrow while retaining its
underlying displayed arrow and whether it is traversed inversely. -/
def signedArrowLetter {x y : Q} (e : SignedArrow x y) :
    SignedGenerator Q × Bool :=
  match e with
  | Sum.inl a => (⟨x, y, a⟩, false)
  | Sum.inr a => (⟨y, x, a⟩, true)

@[simp]
theorem signedArrowLetter_reverse {x y : Q} (e : SignedArrow x y) :
    signedArrowLetter (Quiver.reverse e) =
      ((signedArrowLetter e).1, !(signedArrowLetter e).2) := by
  cases e <;> rfl

/-- The erased signed-arrow letter retains the whole dependent signed arrow. -/
theorem heq_of_signedArrowLetter_eq
    {x y x' y' : Q} {e : SignedArrow x y} {f : SignedArrow x' y'}
    (h : signedArrowLetter e = signedArrowLetter f) : HEq e f := by
  cases e with
  | inl e =>
      cases f with
      | inl f =>
          have hgenerator := congrArg Prod.fst h
          cases hgenerator
          rfl
      | inr f =>
          have hsign := congrArg Prod.snd h
          contradiction
  | inr e =>
      cases f with
      | inl f =>
          have hsign := congrArg Prod.snd h
          contradiction
      | inr f =>
          have hgenerator := congrArg Prod.fst h
          cases hgenerator
          rfl

/-- Equality of erased negative letters retains the underlying displayed
arrows, including their dependent endpoints. -/
theorem heq_of_signedArrowLetter_negativeArrow_eq
    {x y x' y' : Q} {a : x ⟶ y} {b : x' ⟶ y'}
    (h : signedArrowLetter (negativeArrow a) =
      signedArrowLetter (negativeArrow b)) : HEq a b := by
  have hgenerator := congrArg Prod.fst h
  cases hgenerator
  rfl

/-- Equality of erased negative letters identifies the positive copy of the
second arrow with the formal reverse of the negative copy of the first. -/
theorem heq_positiveArrow_reverse_negativeArrow_of_signedArrowLetter_eq
    {x y x' y' : Q} {a : x ⟶ y} {b : x' ⟶ y'}
    (h : signedArrowLetter (negativeArrow a) =
      signedArrowLetter (negativeArrow b)) :
    HEq (positiveArrow b) (Quiver.reverse (negativeArrow a)) := by
  have hgenerator := congrArg Prod.fst h
  cases hgenerator
  rfl

/-- The free-group word of a signed path, listed from its final letter
backwards to match `Quiver.Path` recursion. -/
def signedPathWord {x : Quiver.Symmetrify Q} :
    ∀ {y : Quiver.Symmetrify Q},
      @Quiver.Path (Quiver.Symmetrify Q) (Quiver.symmetrifyQuiver Q) x y →
        List (SignedGenerator Q × Bool)
  | _, Quiver.Path.nil => []
  | _, Quiver.Path.cons p e => signedArrowLetter e :: signedPathWord p

@[simp]
theorem signedPathWord_comp
    {x y z : Quiver.Symmetrify Q}
    (p : @Quiver.Path (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) x y)
    (q : @Quiver.Path (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) y z) :
    signedPathWord (p.comp q) = signedPathWord q ++ signedPathWord p := by
  induction q with
  | nil => simp [signedPathWord]
  | cons q e ih => simp [signedPathWord, ih]

@[simp]
theorem signedPathWord_toPath {x y : Q} (e : SignedArrow x y) :
    signedPathWord e.toPath = [signedArrowLetter e] :=
  rfl

@[simp]
theorem signedPathWord_reverse
    {x y : Q} (p : SignedPath x y) :
    signedPathWord p.reverse = FreeGroup.invRev (signedPathWord p) := by
  induction hlength : p.length using Nat.strong_induction_on generalizing x y with
  | h n ih =>
    cases p with
    | nil => rfl
    | @cons middle _ p e =>
      change Q at middle
      have hlt : p.length < n := by
        simp only [Quiver.Path.length_cons] at hlength
        omega
      have ihp := ih p.length hlt p rfl
      simp only [Quiver.Path.reverse, signedPathWord_comp,
        signedPathWord_toPath, ihp, signedArrowLetter_reverse]
      change FreeGroup.invRev (signedPathWord p) ++
          [((signedArrowLetter e).1, !(signedArrowLetter e).2)] =
        FreeGroup.invRev (signedArrowLetter e :: signedPathWord p)
      rw [FreeGroup.invRev_cons]
      rfl

@[simp]
theorem signedPathWord_length
    {x y : Quiver.Symmetrify Q}
    (p : @Quiver.Path (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) x y) :
    (signedPathWord p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [signedPathWord, ih]

/-- Adjacent letters in a reduced signed path cannot be opposite
orientations of the same displayed generator. -/
theorem IsReduced.signedArrowLetter_sign_eq_of_cons
    {a b c d : Q} (q : SignedPath a b)
    (f : SignedArrow b c) (e : SignedArrow c d)
    (hred : IsReduced ((q.cons f).cons e))
    (hgenerator : (signedArrowLetter e).1 = (signedArrowLetter f).1) :
    (signedArrowLetter e).2 = (signedArrowLetter f).2 := by
  cases e with
  | inl e =>
      cases f with
      | inl f => rfl
      | inr f =>
          cases hgenerator
          exfalso
          apply hred (negativeArrow f : SignedArrow b c)
          refine ⟨q, Quiver.Path.nil, ?_⟩
          simp only [Quiver.Path.comp_nil, Quiver.Path.comp_cons,
            Quiver.Path.comp_toPath_eq_cons, negativeArrow,
            Quiver.symmetrify_reverse, Sum.swap_inr]
  | inr e =>
      cases f with
      | inl f =>
          cases hgenerator
          exfalso
          apply hred (positiveArrow f : SignedArrow b c)
          refine ⟨q, Quiver.Path.nil, ?_⟩
          simp only [Quiver.Path.comp_nil, Quiver.Path.comp_cons,
            Quiver.Path.comp_toPath_eq_cons, positiveArrow,
            Quiver.symmetrify_reverse, Sum.swap_inl]
      | inr f => rfl

/-- A reduced signed path gives a reduced word in the free group on all
displayed arrows. -/
theorem IsReduced.signedPathWord_isReduced {x y : Q}
    (p : SignedPath x y) (hred : IsReduced p) :
    FreeGroup.IsReduced (signedPathWord p) := by
  induction hlength : p.length using Nat.strong_induction_on generalizing x y with
  | h n ih =>
    cases p with
    | nil => exact FreeGroup.IsReduced.nil
    | @cons middle _ p e =>
      change Q at middle
      have hn : p.length + 1 = n := by
        simpa only [Quiver.Path.length_cons] using hlength
      have hpSub : IsContiguousSubpath p (p.cons e) := by
        refine ⟨Quiver.Path.nil, e.toPath, ?_⟩
        simp only [Quiver.Path.nil_comp,
          Quiver.Path.comp_toPath_eq_cons]
      have hpRed : IsReduced p := hred.of_contiguousSubpath hpSub
      have hpWordRed : FreeGroup.IsReduced (signedPathWord p) := by
        exact ih p.length (by omega) p hpRed rfl
      cases p with
      | nil => exact FreeGroup.IsReduced.singleton
      | @cons prior _ q f =>
          change Q at prior
          change FreeGroup.IsReduced
            (signedArrowLetter e :: signedArrowLetter f :: signedPathWord q)
          rw [FreeGroup.isReduced_cons_cons]
          constructor
          · intro hgenerator
            exact hred.signedArrowLetter_sign_eq_of_cons q f e hgenerator
          · exact hpWordRed

private theorem FreeGroup.IsReduced.eq_nil_of_eq_invRev
    {α : Type u} {w : List (α × Bool)} (hred : FreeGroup.IsReduced w)
    (hreverse : w = FreeGroup.invRev w) : w = [] := by
  classical
  have hmk : FreeGroup.mk w = (FreeGroup.mk w)⁻¹ := by
    calc
      FreeGroup.mk w = FreeGroup.mk (FreeGroup.invRev w) :=
        congrArg FreeGroup.mk hreverse
      _ = (FreeGroup.mk w)⁻¹ := FreeGroup.inv_mk.symm
  have hone : FreeGroup.mk w = 1 := self_eq_inv.mp hmk
  have hword := congrArg FreeGroup.toWord hone
  rw [FreeGroup.toWord_mk, FreeGroup.toWord_one,
    hred.reduce_eq] at hword
  exact hword

/-- A reduced signed path whose erased signed-arrow word is equal to its
inverse reversal has length zero.  This form is useful before the two path
endpoints have been identified. -/
theorem IsReduced.length_eq_zero_of_signedPathWord_eq_invRev
    {x y : Q} (p : SignedPath x y) (hred : IsReduced p)
    (hreverse : signedPathWord p =
      FreeGroup.invRev (signedPathWord p)) :
    p.length = 0 := by
  have hnil := FreeGroup.IsReduced.eq_nil_of_eq_invRev
    (IsReduced.signedPathWord_isReduced p hred) hreverse
  have hlength := congrArg List.length hnil
  simpa only [signedPathWord_length, List.length_nil] using hlength

/-- A reduced loop which is equal to its formal reverse has length zero. -/
theorem IsReduced.length_eq_zero_of_eq_reverse {x : Q}
    (p : SignedPath x x) (hred : IsReduced p) (hreverse : p = p.reverse) :
    p.length = 0 := by
  have hwordReverse : signedPathWord p =
      FreeGroup.invRev (signedPathWord p) := by
    rw [← signedPathWord_reverse]
    exact congrArg signedPathWord hreverse
  exact hred.length_eq_zero_of_signedPathWord_eq_invRev p hwordReverse

end MagnitudeConjecture.BoundQuiver.StringWord
