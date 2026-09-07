import MagnitudeConjecture.Algebra.StringDetectorFunctor

/-!
# Indices for finite-string detectors

Butler--Ringel choose one representative of string words modulo formal
inversion.  This file packages the endpoint-polarized words, defines that
equivalence relation through their underlying literal words, and attaches the
already constructed detector functor to a chosen representative of each
quotient class.

The quotient identifies the two polarized length-zero words at a vertex,
since they are formal inverses in the source convention.  No band indices are
needed: finite detector reconstruction directly proves object coverage in
the representation-finite branch.
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

namespace EndpointWord

/-- Give an arbitrary literal word its intrinsic target sign.  For the empty
word we choose `false`; the quotient index below identifies this choice with
the oppositely polarized trivial word. -/
def ofWord (S : P.ArrowPolarization)
    (C : Word P.toPresentation.relations) :
    EndpointWord S C.target (signedPathTargetSignOr S false C.path) where
  source := C.source
  path := C.path
  isString := C.isString
  targetSign_eq := by
    unfold signedPathTargetSignOr
    cases h : signedPathTargetSign S C.path <;> simp

@[simp]
theorem ofWord_word (S : P.ArrowPolarization)
    (C : Word P.toPresentation.relations) :
    (ofWord S C).word = C := by
  apply Word.ext <;> rfl

/-- Forgetting a fixed endpoint polarization is injective on endpoint
words. -/
theorem word_injective (S : P.ArrowPolarization) {u : Q} {t : Bool} :
    Function.Injective
      (EndpointWord.word : EndpointWord S u t →
        Word P.toPresentation.relations) := by
  rintro ⟨source, path, hstring, hsign⟩
    ⟨source', path', hstring', hsign'⟩ h
  dsimp only [EndpointWord.word] at h
  cases h
  rfl

end EndpointWord

/-- All endpoint-polarized finite string words. -/
abbrev DetectorWord (S : P.ArrowPolarization) :=
  Σ u : Q, Σ t : Bool, EndpointWord S u t

namespace DetectorWord

variable {S : P.ArrowPolarization}

/-- Forget the endpoint and sign indices. -/
def underlying (C : DetectorWord S) : Word P.toPresentation.relations :=
  C.2.2.word

/-- Regard an arbitrary literal word as a detector word. -/
def ofWord (S : P.ArrowPolarization)
    (C : Word P.toPresentation.relations) : DetectorWord S :=
  ⟨C.target, signedPathTargetSignOr S false C.path,
    EndpointWord.ofWord S C⟩

@[simp]
theorem ofWord_underlying (S : P.ArrowPolarization)
    (C : Word P.toPresentation.relations) :
    (ofWord S C).underlying = C :=
  EndpointWord.ofWord_word S C

/-- Equivalence of detector words under formal inversion. -/
def InverseEquivalent (C D : DetectorWord S) : Prop :=
  C.underlying = D.underlying ∨ C.underlying = D.underlying.reverse

theorem inverseEquivalent_refl (C : DetectorWord S) :
    C.InverseEquivalent C :=
  Or.inl rfl

theorem inverseEquivalent_symm {C D : DetectorWord S}
    (h : C.InverseEquivalent D) : D.InverseEquivalent C := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    have hreverse := congrArg
      (fun W : Word P.toPresentation.relations ↦ W.reverse) h
    have hreverse' : C.underlying.reverse = D.underlying := by
      simpa using hreverse
    exact hreverse'.symm

theorem inverseEquivalent_trans {C D E : DetectorWord S}
    (hCD : C.InverseEquivalent D) (hDE : D.InverseEquivalent E) :
    C.InverseEquivalent E := by
  rcases hCD with hCD | hCD <;> rcases hDE with hDE | hDE
  · exact Or.inl (hCD.trans hDE)
  · exact Or.inr (hCD.trans hDE)
  · right
    exact hCD.trans (congrArg
      (fun W : Word P.toPresentation.relations ↦ W.reverse) hDE)
  · left
    calc
      C.underlying = D.underlying.reverse := hCD
      _ = E.underlying.reverse.reverse := congrArg
        (fun W : Word P.toPresentation.relations ↦ W.reverse) hDE
      _ = E.underlying := E.underlying.reverse_reverse

/-- Setoid of finite strings modulo formal inversion. -/
def inverseSetoid (S : P.ArrowPolarization) : Setoid (DetectorWord S) where
  r := InverseEquivalent
  iseqv := {
    refl := inverseEquivalent_refl
    symm := inverseEquivalent_symm
    trans := inverseEquivalent_trans }

end DetectorWord

/-- The index type for finite-string detecting functors. -/
def DetectorIndex (S : P.ArrowPolarization) :=
  Quotient (DetectorWord.inverseSetoid S)

namespace DetectorIndex

variable {S : P.ArrowPolarization}

/-- The detector index of a literal word. -/
def ofWord (S : P.ArrowPolarization)
    (C : Word P.toPresentation.relations) : DetectorIndex S :=
  Quotient.mk'' (DetectorWord.ofWord S C)

/-- A word and its formal inverse determine the same detector index. -/
theorem ofWord_reverse (S : P.ArrowPolarization)
    (C : Word P.toPresentation.relations) :
    ofWord S C.reverse = ofWord S C := by
  apply Quotient.sound
  right
  simp

/-- Equality of word indices is exactly equality up to formal inversion. -/
theorem ofWord_eq_iff (S : P.ArrowPolarization)
    (C D : Word P.toPresentation.relations) :
    ofWord S C = ofWord S D ↔ C = D ∨ C = D.reverse := by
  unfold ofWord DetectorIndex
  rw [Quotient.eq'']
  rfl

/-- Every finite-string detector index is represented by a literal word. -/
theorem ofWord_surjective (S : P.ArrowPolarization) :
    Function.Surjective (ofWord S) := by
  intro i
  let D := Quotient.out i
  refine ⟨D.underlying, ?_⟩
  rw [← Quotient.out_eq i]
  apply Quotient.sound
  exact Or.inl (DetectorWord.ofWord_underlying S D.underlying)

/-- A noncanonical representative of a detector index, matching the source's
choice of a representative set. -/
def representative (i : DetectorIndex S) : DetectorWord S :=
  Quotient.out i

/-- The chosen representative belongs to the requested quotient class. -/
theorem mk_representative (i : DetectorIndex S) :
    Quotient.mk'' i.representative = i :=
  Quotient.out_eq i

/-- The endpoint-polarized word selected by an index. -/
def endpointWord (i : DetectorIndex S) :
    EndpointWord S i.representative.1 i.representative.2.1 :=
  i.representative.2.2

/-- Reindexing the underlying word of the chosen representative recovers the
original detector index. -/
@[simp]
theorem ofWord_endpointWord (i : DetectorIndex S) :
    ofWord S i.endpointWord.word = i := by
  have hunderlying :
      (DetectorWord.ofWord S i.endpointWord.word).underlying =
        i.representative.underlying := by
    rw [DetectorWord.ofWord_underlying]
    rfl
  have hrepresentative : ofWord S i.endpointWord.word =
      (Quotient.mk'' i.representative : DetectorIndex S) :=
    Quotient.sound (Or.inl hunderlying)
  exact hrepresentative.trans (mk_representative i)

/-- The finite-string detector attached to the chosen representative of an
inversion class. -/
def detectorFunctor (i : DetectorIndex S) :
    MagnitudeConjecture.CoveringHom.LinearModuleCategory
        (C := (Category P.toPresentation.relations)ᵒᵖ) k ⥤
      ModuleCat.{u} k :=
  i.endpointWord.detectorFunctor

end DetectorIndex

end MagnitudeConjecture.BoundQuiver.StringWord
