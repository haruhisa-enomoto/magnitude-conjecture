import MagnitudeConjecture.Algebra.StringPathCombinatorics
import MagnitudeConjecture.Algebra.StringWord
import Mathlib.Logic.Equiv.Defs

/-!
# Butler--Ringel arrow polarizations

Butler and Ringel choose two signs on the arrows of a string quiver.  Arrows
with a common source have distinct source signs, arrows with a common target
have distinct target signs, and a surviving two-arrow path has opposite signs
at its middle vertex.  The special-biserial degree and continuation bounds
are exactly what is needed to make such a choice.

We encode the two signs by `Bool`; Boolean negation is the source's change of
sign.  This file proves that every special-biserial presentation admits the
choice, so polarization is data derived from the presentation rather than an
extra hypothesis on later detector theorems.
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

/-- An outgoing and an incoming arrow at `u` are compatible when their
two-arrow path survives the relation quotient. -/
def CompatibleAt
    (P : SpecialBiserialPresentation k A Q) {u : Q}
    (out : Quiver.Star u) (inc : Quiver.Costar u) : Prop :=
  arrowMap P.toPresentation.relations out.2 ≫
      arrowMap P.toPresentation.relations inc.2 ≠ 0

/-- A choice of Butler--Ringel signs at one vertex. -/
structure VertexPolarization
    (P : SpecialBiserialPresentation k A Q) (u : Q) where
  sourceSign : Quiver.Star u → Bool
  targetSign : Quiver.Costar u → Bool
  sourceSign_injective : Function.Injective sourceSign
  targetSign_injective : Function.Injective targetSign
  compatible_sign : ∀ (out : Quiver.Star u) (inc : Quiver.Costar u),
    P.CompatibleAt out inc → sourceSign out = Bool.not (targetSign inc)

/-- A Butler--Ringel arrow polarization, assembled independently at every
displayed vertex. -/
structure ArrowPolarization
    (P : SpecialBiserialPresentation k A Q) where
  atVertex : ∀ u : Q, P.VertexPolarization u

namespace ArrowPolarization

variable {P : SpecialBiserialPresentation k A Q}

/-- The source sign `sigma(a)` of an ordinary arrow. -/
def sourceSign (S : P.ArrowPolarization) {x y : Q} (a : x ⟶ y) : Bool :=
  (S.atVertex x).sourceSign ⟨y, a⟩

/-- The target sign `epsilon(a)` of an ordinary arrow. -/
def targetSign (S : P.ArrowPolarization) {x y : Q} (a : x ⟶ y) : Bool :=
  (S.atVertex y).targetSign ⟨x, a⟩

/-- Distinct arrows with a common source have distinct source signs. -/
theorem sourceSign_ne
    (S : P.ArrowPolarization) {x y z : Q}
    {a : x ⟶ y} {b : x ⟶ z}
    (hab : (⟨y, a⟩ : Quiver.Star x) ≠ ⟨z, b⟩) :
    S.sourceSign a ≠ S.sourceSign b := by
  intro hsign
  exact hab ((S.atVertex x).sourceSign_injective hsign)

/-- Distinct arrows with a common target have distinct target signs. -/
theorem targetSign_ne
    (S : P.ArrowPolarization) {x y z : Q}
    {a : x ⟶ z} {b : y ⟶ z}
    (hab : (⟨x, a⟩ : Quiver.Costar z) ≠ ⟨y, b⟩) :
    S.targetSign a ≠ S.targetSign b := by
  intro hsign
  exact hab ((S.atVertex z).targetSign_injective hsign)

/-- A surviving composition has opposite signs at its middle vertex. -/
theorem sourceSign_eq_not_targetSign
    (S : P.ArrowPolarization) {x y z : Q}
    (a : x ⟶ y) (b : y ⟶ z)
    (hcomp : arrowMap P.toPresentation.relations b ≫
        arrowMap P.toPresentation.relations a ≠ 0) :
    S.sourceSign b = Bool.not (S.targetSign a) :=
  (S.atVertex y).compatible_sign ⟨z, b⟩ ⟨x, a⟩ hcomp

end ArrowPolarization

/-- Equality with a marked element gives an injective Boolean label on any
finite type with at most two elements. -/
private theorem marker_injective
    {T : Type*} [Finite T] [DecidableEq T]
    (base : T) (hcard : Nat.card T ≤ 2) :
    Function.Injective (fun x : T ↦ decide (x = base)) := by
  classical
  intro x y hxy
  by_cases hx : x = base
  · subst x
    have hy : y = base := by
      by_contra hy
      simp [hy] at hxy
    exact hy.symm
  · have hy : y ≠ base := by
      intro hy
      subst y
      simp [hx] at hxy
    by_contra hne
    letI : Fintype T := Fintype.ofFinite T
    let f : Fin 3 → T := ![base, x, y]
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [f]
    have hthree : 3 ≤ Fintype.card T := by
      simpa using Fintype.card_le_of_injective f hf
    have htwo : Fintype.card T ≤ 2 := by
      simpa only [Nat.card_eq_fintype_card] using hcard
    omega

/-- Every finite type of cardinality at most two admits an injective Boolean
label. -/
private theorem exists_boolLabel
    (T : Type*) [Finite T] (hcard : Nat.card T ≤ 2) :
    ∃ f : T → Bool, Function.Injective f := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  let hcard' : Fintype.card T ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  let f : T → Bool := fun x ↦
    finTwoEquiv (Fin.castLE hcard' (Fintype.equivFin T x))
  refine ⟨f, ?_⟩
  intro x y hxy
  apply (Fintype.equivFin T).injective
  apply Fin.castLE_injective hcard'
  exact finTwoEquiv.injective hxy

/-- The degree-two and unique-continuation axioms produce a polarization at
each vertex. -/
theorem exists_vertexPolarization
    (P : SpecialBiserialPresentation k A Q) (u : Q) :
    Nonempty (P.VertexPolarization u) := by
  classical
  by_cases hpair : ∃ (out : Quiver.Star u) (inc : Quiver.Costar u),
      P.CompatibleAt out inc
  · rcases hpair with ⟨out₀, inc₀, h₀⟩
    let sourceSign : Quiver.Star u → Bool :=
      fun out ↦ decide (out = out₀)
    let targetSign : Quiver.Costar u → Bool :=
      fun inc ↦ Bool.not (decide (inc = inc₀))
    refine ⟨{
      sourceSign := sourceSign
      targetSign := targetSign
      sourceSign_injective := marker_injective out₀ (P.arrows_starting_le_two u)
      targetSign_injective := ?_
      compatible_sign := ?_ }⟩
    · intro inc₁ inc₂ hsign
      apply marker_injective inc₀ (P.arrows_ending_le_two u)
      exact Bool.involutive_not.injective hsign
    · intro out inc hcomp
      by_cases hout : out = out₀
      · subst out
        have hinc : inc = inc₀ := by
          let left₁ : P.LeftContinuationArrow out₀.2 := ⟨inc, hcomp⟩
          let left₀ : P.LeftContinuationArrow out₀.2 := ⟨inc₀, h₀⟩
          have hleft := @Subsingleton.elim _
            (P.leftContinuationArrow_subsingleton out₀.2) left₁ left₀
          exact congrArg (fun c : P.LeftContinuationArrow out₀.2 ↦ c.1) hleft
        subst inc
        simp [sourceSign, targetSign]
      · have hinc : inc ≠ inc₀ := by
          intro hinc
          subst inc
          let right₁ : P.RightContinuationArrow inc₀.2 := ⟨out, hcomp⟩
          let right₀ : P.RightContinuationArrow inc₀.2 := ⟨out₀, h₀⟩
          have hright := @Subsingleton.elim _
            (P.rightContinuationArrow_subsingleton inc₀.2) right₁ right₀
          exact hout (congrArg
            (fun c : P.RightContinuationArrow inc₀.2 ↦ c.1) hright)
        simp [sourceSign, targetSign, hout, hinc]
  · rcases exists_boolLabel (Quiver.Star u)
        (P.arrows_starting_le_two u) with ⟨sourceSign, hsource⟩
    rcases exists_boolLabel (Quiver.Costar u)
        (P.arrows_ending_le_two u) with ⟨targetSign, htarget⟩
    refine ⟨{
      sourceSign := sourceSign
      targetSign := targetSign
      sourceSign_injective := hsource
      targetSign_injective := htarget
      compatible_sign := ?_ }⟩
    intro out inc hcomp
    exact False.elim (hpair ⟨out, inc, hcomp⟩)

/-- Every special-biserial presentation admits Butler--Ringel arrow signs.
The choice is noncanonical, as in the source. -/
theorem nonempty_arrowPolarization
    (P : SpecialBiserialPresentation k A Q) :
    Nonempty P.ArrowPolarization := by
  classical
  exact ⟨{
    atVertex := fun u ↦ Classical.choice (P.exists_vertexPolarization u) }⟩

/-- A fixed noncanonical Butler--Ringel polarization of a special-biserial
presentation. -/
def arrowPolarization
    (P : SpecialBiserialPresentation k A Q) : P.ArrowPolarization :=
  Classical.choice P.nonempty_arrowPolarization

end SpecialBiserialPresentation

namespace StringWord

variable {P : SpecialBiserialPresentation k A Q}

/-- Butler--Ringel's source sign of a signed arrow.  Formal inversion swaps
the source and target signs of the underlying ordinary arrow. -/
def signedArrowSourceSign
    (S : P.ArrowPolarization) {x y : Q} (e : SignedArrow x y) : Bool :=
  match e with
  | Sum.inl a => S.sourceSign a
  | Sum.inr a => S.targetSign a

/-- Butler--Ringel's target sign of a signed arrow. -/
def signedArrowTargetSign
    (S : P.ArrowPolarization) {x y : Q} (e : SignedArrow x y) : Bool :=
  match e with
  | Sum.inl a => S.targetSign a
  | Sum.inr a => S.sourceSign a

@[simp]
theorem signedArrowSourceSign_positive
    (S : P.ArrowPolarization) {x y : Q} (a : x ⟶ y) :
    signedArrowSourceSign S (positiveArrow a) = S.sourceSign a :=
  rfl

@[simp]
theorem signedArrowSourceSign_negative
    (S : P.ArrowPolarization) {x y : Q} (a : x ⟶ y) :
    signedArrowSourceSign S (negativeArrow a) = S.targetSign a :=
  rfl

@[simp]
theorem signedArrowTargetSign_positive
    (S : P.ArrowPolarization) {x y : Q} (a : x ⟶ y) :
    signedArrowTargetSign S (positiveArrow a) = S.targetSign a :=
  rfl

@[simp]
theorem signedArrowTargetSign_negative
    (S : P.ArrowPolarization) {x y : Q} (a : x ⟶ y) :
    signedArrowTargetSign S (negativeArrow a) = S.sourceSign a :=
  rfl

@[simp]
theorem signedArrowTargetSign_reverse
    (S : P.ArrowPolarization) {x y : Q} (e : SignedArrow x y) :
    signedArrowTargetSign S (Quiver.reverse e) =
      signedArrowSourceSign S e := by
  cases e <;> rfl

@[simp]
theorem signedArrowSourceSign_reverse
    (S : P.ArrowPolarization) {x y : Q} (e : SignedArrow x y) :
    signedArrowSourceSign S (Quiver.reverse e) =
      signedArrowTargetSign S e := by
  cases e <;> rfl

/-- Consecutive letters of a string have opposite Butler--Ringel signs at
their common vertex.  For equally oriented letters this is the polarization
condition on a surviving ordinary two-arrow path.  For oppositely oriented
letters, reducedness and injectivity of the relevant endpoint signs give the
same conclusion. -/
theorem signedArrowSourceSign_eq_not_targetSign_of_isString
    (S : P.ArrowPolarization) {x y z : Q}
    (e : SignedArrow x y) (f : SignedArrow y z)
    (hstring : IsString P.toPresentation.relations
      (e.toPath.comp f.toPath)) :
    signedArrowSourceSign S f =
      Bool.not (signedArrowTargetSign S e) := by
  cases e with
  | inl a =>
      cases f with
      | inl b =>
          apply S.sourceSign_eq_not_targetSign a b
          rw [arrowMap, arrowMap, pathMap_comp]
          apply hstring.2.1 (a.toPath.comp b.toPath)
          change IsContiguousSubpath
            ((positiveArrow a).toPath.comp (positiveArrow b).toPath)
            ((positiveArrow a).toPath.comp (positiveArrow b).toPath)
          exact isContiguousSubpath_refl _
      | inr b =>
          rw [Bool.eq_not_iff]
          apply S.targetSign_ne
          intro hcostar
          cases hcostar
          apply hstring.1 (positiveArrow a)
          exact isContiguousSubpath_refl _
  | inr a =>
      cases f with
      | inl b =>
          rw [Bool.eq_not_iff]
          apply S.sourceSign_ne
          intro hstar
          cases hstar
          apply hstring.1 (negativeArrow a)
          exact isContiguousSubpath_refl _
      | inr b =>
          have hcomp : arrowMap P.toPresentation.relations a ≫
              arrowMap P.toPresentation.relations b ≠ 0 := by
            rw [arrowMap, arrowMap, pathMap_comp]
            apply hstring.2.2 (b.toPath.comp a.toPath)
            change IsContiguousSubpath
              ((positiveArrow b).toPath.comp (positiveArrow a).toPath)
              (((negativeArrow a).toPath.comp
                (negativeArrow b).toPath).reverse)
            simpa only [Quiver.Path.reverse_comp,
              Quiver.Path.reverse_toPath, reverse_negativeArrow] using
                isContiguousSubpath_refl
                  ((positiveArrow b).toPath.comp (positiveArrow a).toPath)
          have hopposite := S.sourceSign_eq_not_targetSign b a hcomp
          change S.targetSign b = Bool.not (S.sourceSign a)
          cases hsign : S.targetSign b <;> simp_all

/-- Target sign of a nonempty signed path.  The empty path has no intrinsic
sign; its two Butler--Ringel polarizations are supplied separately below. -/
def signedPathTargetSign
    (S : P.ArrowPolarization) :
    {x y : Q} → SignedPath x y → Option Bool
  | _, _, Quiver.Path.nil => none
  | _, _, Quiver.Path.cons _ e => some (signedArrowTargetSign S e)

/-- Source sign of a nonempty signed path, defined as the target sign of its
formal inverse. -/
def signedPathSourceSign
    (S : P.ArrowPolarization) {x y : Q} (p : SignedPath x y) : Option Bool :=
  signedPathTargetSign S p.reverse

@[simp]
theorem signedPathTargetSign_nil
    (S : P.ArrowPolarization) (x : Q) :
    signedPathTargetSign S (Quiver.Path.nil : SignedPath x x) = none :=
  rfl

@[simp]
theorem signedPathTargetSign_cons
    (S : P.ArrowPolarization) {x y z : Q}
    (p : SignedPath x y) (e : SignedArrow y z) :
    signedPathTargetSign S (p.cons e) =
      some (signedArrowTargetSign S e) :=
  rfl

@[simp]
theorem signedPathSourceSign_nil
    (S : P.ArrowPolarization) (x : Q) :
    signedPathSourceSign S (Quiver.Path.nil : SignedPath x x) = none := by
  simp [signedPathSourceSign]

@[simp]
theorem signedPathTargetSign_reverse
    (S : P.ArrowPolarization) {x y : Q} (p : SignedPath x y) :
    signedPathTargetSign S p.reverse = signedPathSourceSign S p :=
  rfl

@[simp]
theorem signedPathSourceSign_reverse
    (S : P.ArrowPolarization) {x y : Q} (p : SignedPath x y) :
    signedPathSourceSign S p.reverse = signedPathTargetSign S p := by
  simp [signedPathSourceSign]

/-- The source sign of a path displayed as its first letter followed by a
tail is the source sign of that first letter. -/
@[simp]
theorem signedPathSourceSign_toPath_comp
    (S : P.ArrowPolarization) {x y z : Q}
    (e : SignedArrow x y) (p : SignedPath y z) :
    signedPathSourceSign S (e.toPath.comp p) =
      some (signedArrowSourceSign S e) := by
  unfold signedPathSourceSign
  rw [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
    Quiver.Path.comp_toPath_eq_cons]
  simpa only [signedArrowTargetSign_reverse] using
    signedPathTargetSign_cons S p.reverse (Quiver.reverse e)

/-- If a letter is prefixed to a nonempty string, its target sign is
opposite to the intrinsic source sign of that string. -/
theorem signedPathSourceSign_eq_not_targetSign_of_isString_prepend
    (S : P.ArrowPolarization) {x y z : Q}
    (e : SignedArrow x y) (p : SignedPath y z)
    (hp : 0 < p.length)
    (hstring : IsString P.toPresentation.relations
      (e.toPath.comp p)) :
    signedPathSourceSign S p =
      some (Bool.not (signedArrowTargetSign S e)) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  obtain ⟨w, f, q, hq, hpq⟩ :=
    p.eq_toPath_comp_of_length_eq_succ hn
  subst p
  have htwo : IsString P.toPresentation.relations
      (e.toPath.comp f.toPath) := by
    apply IsString.of_contiguousSubpath P.toPresentation.relations hstring
    refine ⟨Quiver.Path.nil, q, ?_⟩
    simp only [Quiver.Path.nil_comp, Quiver.Path.comp_assoc]
  rw [signedPathSourceSign_toPath_comp]
  exact congrArg some
    (signedArrowSourceSign_eq_not_targetSign_of_isString S e f htwo)

/-- Dually, if a letter is appended to a nonempty string, its source sign is
opposite to the intrinsic target sign of that string. -/
theorem signedPathTargetSign_eq_not_sourceSign_of_isString_append
    (S : P.ArrowPolarization) {x y z : Q}
    (p : SignedPath x y) (e : SignedArrow y z)
    (hp : 0 < p.length)
    (hstring : IsString P.toPresentation.relations
      (p.comp e.toPath)) :
    signedPathTargetSign S p =
      some (Bool.not (signedArrowSourceSign S e)) := by
  have hreverseString : IsString P.toPresentation.relations
      ((Quiver.reverse e).toPath.comp p.reverse) := by
    rw [← Quiver.Path.reverse_toPath, ← Quiver.Path.reverse_comp]
    exact (isString_reverse_iff P.toPresentation.relations _).2 hstring
  have hsource :=
    signedPathSourceSign_eq_not_targetSign_of_isString_prepend S
      (Quiver.reverse e) p.reverse (by
        rw [length_reverse]
        exact hp) hreverseString
  simpa only [signedPathSourceSign_reverse,
    signedArrowTargetSign_reverse] using hsource

/-- The target sign of a path, using `t` for the empty path. -/
def signedPathTargetSignOr
    (S : P.ArrowPolarization) (t : Bool)
    {x y : Q} (p : SignedPath x y) : Bool :=
  (signedPathTargetSign S p).getD t

/-- The source sign of a path, using `t` for the empty path. -/
def signedPathSourceSignOr
    (S : P.ArrowPolarization) (t : Bool)
    {x y : Q} (p : SignedPath x y) : Bool :=
  (signedPathSourceSign S p).getD t

/-- Butler--Ringel's `W(u,t)`: a string ending at `u` with target sign `t`.
For a length-zero word, `t` chooses one of the two formal trivial strings;
for a nonempty word, its last signed arrow determines `t`. -/
structure EndpointWord
    (S : P.ArrowPolarization) (u : Q) (t : Bool) where
  source : Q
  path : SignedPath source u
  isString : IsString P.toPresentation.relations path
  targetSign_eq : signedPathTargetSignOr S t path = t

namespace EndpointWord

variable {S : P.ArrowPolarization} {u : Q} {t : Bool}

/-- Forget the endpoint polarization and recover the underlying string word. -/
def word (C : EndpointWord S u t) : Word P.toPresentation.relations where
  source := C.source
  target := u
  path := C.path
  isString := C.isString

/-- Butler--Ringel's source sign.  For the trivial word `1_(u,t)` it is
`not t`; otherwise it is the sign of the first signed arrow. -/
def sourceSign (C : EndpointWord S u t) : Bool :=
  signedPathSourceSignOr S (Bool.not t) C.path

/-- The two formal length-zero strings at a vertex. -/
def vertex
    (P : SpecialBiserialPresentation k A Q)
    (S : P.ArrowPolarization) (u : Q) (t : Bool) : EndpointWord S u t where
  source := u
  path := Quiver.Path.nil
  isString := (Word.vertex P.toPresentation.relations
    P.toPresentation.admissible u).isString
  targetSign_eq := rfl

@[simp]
theorem vertex_sourceSign
    (P : SpecialBiserialPresentation k A Q)
    (S : P.ArrowPolarization) (u : Q) (t : Bool) :
    (vertex P S u t).sourceSign = Bool.not t := by
  rfl

end EndpointWord

end StringWord

end MagnitudeConjecture.BoundQuiver
