import MagnitudeConjecture.Algebra.StringDetectorFunctor
import MagnitudeConjecture.Algebra.StringMorphismCoefficient
import MagnitudeConjecture.Algebra.StringRepresentation

/-!
# Transporting the distinguished basis vector along its own string

The self-evaluation of a Butler--Ringel detector rests on one elementary
calculation: starting with the source-position basis vector of a literal
string module and transporting its span along any prefix of the same word
reaches the basis vector at the end of that prefix.  Positive letters use the
displayed-arrow image; inverse letters use its preimage.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

namespace Word

/-- If the inverse of an outgoing arrow can be prefixed to a string, that
arrow kills the string module's source-position basis vector. -/
theorem not_exists_arrowStep_sourcePosition_of_prepend_negative_isString
    (D : Word R) {y : Q} (a : D.source ⟶ y)
    (hstring : IsString R
      ((negativeArrow a).toPath.comp D.path)) :
    ¬ ∃ j : D.PositionAt y, D.ArrowStep a D.sourcePosition j := by
  rintro ⟨j, hstep⟩
  rcases hstep with hpositive | hnegative
  · rcases j.2 with ⟨q, hq⟩
    apply hstring.1 (negativeArrow a)
    refine ⟨Quiver.Path.nil, q, ?_⟩
    simp only [Quiver.Path.nil_comp, Quiver.Path.comp_assoc,
      reverse_negativeArrow]
    calc
      (negativeArrow a).toPath.comp D.path =
          (negativeArrow a).toPath.comp (j.1.comp q) :=
        congrArg (fun p ↦ (negativeArrow a).toPath.comp p) hq
      _ = (negativeArrow a).toPath.comp
          ((D.sourcePosition.1.comp (positiveArrow a).toPath).comp q) :=
        congrArg
          (fun p ↦ (negativeArrow a).toPath.comp (p.comp q)) hpositive
      _ = ((negativeArrow a).toPath.comp
          (positiveArrow a).toPath).comp q := by
        simp only [sourcePosition, Quiver.Path.nil_comp,
          Quiver.Path.comp_assoc]
      _ = (negativeArrow a).toPath.comp
          ((positiveArrow a).toPath.comp q) :=
        Quiver.Path.comp_assoc _ _ _
  · have hlength := congrArg Quiver.Path.length hnegative
    simp only [sourcePosition, Quiver.Path.length_nil,
      Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
    omega

/-- Concrete arrow-map form of the preceding no-step statement. -/
theorem arrowLinearMap_sourceBasis_eq_zero_of_prepend_negative_isString
    (D : Word R) {y : Q} (a : D.source ⟶ y)
    (hstring : IsString R
      ((negativeArrow a).toPath.comp D.path)) :
    D.arrowLinearMap a
        (Finsupp.single D.sourcePosition (1 : k)) = 0 := by
  rw [D.arrowLinearMap_single]
  rw [D.arrowOnBasis_eq_zero_of_not_exists a D.sourcePosition
    (D.not_exists_arrowStep_sourcePosition_of_prepend_negative_isString
      a hstring)]
  simp

/-- If an incoming arrow can be prefixed positively to a string, no position
of the string maps to its source-position coordinate along that arrow. -/
theorem not_exists_arrowStep_to_sourcePosition_of_prepend_positive_isString
    (D : Word R) {x : Q} (a : x ⟶ D.source)
    (hstring : IsString R
      ((positiveArrow a).toPath.comp D.path)) :
    ¬ ∃ i : D.PositionAt x, D.ArrowStep a i D.sourcePosition := by
  rintro ⟨i, hstep⟩
  rcases hstep with hpositive | hnegative
  · have hlength := congrArg Quiver.Path.length hpositive
    simp only [sourcePosition, Quiver.Path.length_nil,
      Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
    omega
  · rcases i.2 with ⟨q, hq⟩
    apply hstring.1 (positiveArrow a)
    refine ⟨Quiver.Path.nil, q, ?_⟩
    simp only [Quiver.Path.nil_comp, Quiver.Path.comp_assoc,
      reverse_positiveArrow]
    calc
      (positiveArrow a).toPath.comp D.path =
          (positiveArrow a).toPath.comp (i.1.comp q) :=
        congrArg (fun p ↦ (positiveArrow a).toPath.comp p) hq
      _ = (positiveArrow a).toPath.comp
          ((D.sourcePosition.1.comp (negativeArrow a).toPath).comp q) :=
        congrArg
          (fun p ↦ (positiveArrow a).toPath.comp (p.comp q)) hnegative
      _ = ((positiveArrow a).toPath.comp
          (negativeArrow a).toPath).comp q := by
        simp only [sourcePosition, Quiver.Path.nil_comp,
          Quiver.Path.comp_assoc]
      _ = (positiveArrow a).toPath.comp
          ((negativeArrow a).toPath.comp q) :=
        Quiver.Path.comp_assoc _ _ _

/-- Every image along such an incoming arrow has zero source-position
coefficient. -/
theorem arrowLinearMap_apply_sourcePosition_eq_zero_of_prepend_positive_isString
    (D : Word R) {x : Q} (a : x ⟶ D.source) (v : D.Space x)
    (hstring : IsString R
      ((positiveArrow a).toPath.comp D.path)) :
    D.arrowLinearMap a v D.sourcePosition = 0 := by
  exact D.arrowLinearMap_apply_eq_zero_of_not_exists_source a v
    D.sourcePosition
      (D.not_exists_arrowStep_to_sourcePosition_of_prepend_positive_isString
        a hstring)

/-- On a literal string module, the general displayed-arrow map is its
position-basis arrow map. -/
@[simp]
theorem moduleArrowMap_rightModule
    (D : Word R) (hmono : IsMonomial R)
    {x y : Q} (a : x ⟶ y) :
    moduleArrowMap (D.rightModule hmono) a =
      ModuleCat.ofHom (D.arrowLinearMap a) := by
  unfold moduleArrowMap BoundQuiver.arrowMap
  rw [D.rightModule_map_pathMap, D.quiverMap_toPath]

/-- The distinguished basis vector at the end of a prefix belongs to the
transport, along that prefix, of the source-position line. -/
theorem prefixBasis_mem_signedPathSubspace_span_source
    (D : Word R) (hmono : IsMonomial R) :
    ∀ {x : Q} (p : SignedPath D.source x)
      (q : SignedPath x D.target) (hp : D.path = p.comp q),
      Finsupp.single
          (⟨p, q, hp⟩ : D.PositionAt x) (1 : k) ∈
        signedPathSubspace (D.rightModule hmono) p
          (Submodule.span k
            {Finsupp.single D.sourcePosition (1 : k)}) := by
  classical
  intro x p
  induction hlength : p.length using Nat.strong_induction_on generalizing x with
  | h n ih =>
      cases p with
      | nil =>
          intro q hp
          have hposition :
              (⟨Quiver.Path.nil, q, hp⟩ : D.PositionAt D.source) =
                D.sourcePosition := by
            apply PositionAt.ext_index
            rfl
          rw [signedPathSubspace_nil]
          change (Finsupp.single
              (⟨Quiver.Path.nil, q, hp⟩ : D.PositionAt D.source) (1 : k) :
                (D.rightModule hmono).obj
                  (Opposite.op (BoundQuiver.obj R D.source))) ∈
            Submodule.span k {Finsupp.single D.sourcePosition (1 : k)}
          rw [hposition]
          exact Submodule.subset_span (Set.mem_singleton _)
      | @cons y _ p e =>
          change Q at y
          intro q hp
          let previous : D.PositionAt y :=
            ⟨p, e.toPath.comp q, by
              rw [← Quiver.Path.comp_assoc]
              exact hp⟩
          let current : D.PositionAt x := ⟨p.cons e, q, hp⟩
          have hprevious :
              Finsupp.single previous (1 : k) ∈
                signedPathSubspace (D.rightModule hmono) p
                  (Submodule.span k
                    {Finsupp.single D.sourcePosition (1 : k)}) := by
            have hlt : p.length < n := by
              simp only [Quiver.Path.length_cons] at hlength
              omega
            exact ih p.length hlt p rfl (e.toPath.comp q) (by
              rw [← Quiver.Path.comp_assoc]
              exact hp)
          rw [signedPathSubspace_cons]
          cases e with
          | inl a =>
              refine ⟨Finsupp.single previous (1 : k), hprevious, ?_⟩
              rw [D.moduleArrowMap_rightModule hmono a]
              change D.arrowLinearMap a
                (Finsupp.single previous (1 : k)) =
                  Finsupp.single current (1 : k)
              apply D.arrowLinearMap_single_one_of_step
              left
              rfl
          | inr a =>
              simp only [signedArrowSubspace]
              rw [D.moduleArrowMap_rightModule hmono a]
              change D.arrowLinearMap a
                (Finsupp.single current (1 : k)) ∈
                signedPathSubspace (D.rightModule hmono) p
                  (Submodule.span k
                    {Finsupp.single D.sourcePosition (1 : k)})
              rw [D.arrowLinearMap_single_one_of_step a current previous]
              · exact hprevious
              · right
                rfl

/-- In particular, transporting the source-position line along the complete
word reaches the target-position basis vector. -/
theorem targetBasis_mem_signedPathSubspace_span_source
    (D : Word R) (hmono : IsMonomial R) :
    Finsupp.single D.targetPosition (1 : k) ∈
      signedPathSubspace (D.rightModule hmono) D.path
        (Submodule.span k
          {Finsupp.single D.sourcePosition (1 : k)}) := by
  let final : D.PositionAt D.target :=
    ⟨D.path, Quiver.Path.nil, by simp⟩
  have hfinal : final = D.targetPosition := by
    apply PositionAt.ext_index
    rfl
  rw [← hfinal]
  exact D.prefixBasis_mem_signedPathSubspace_span_source hmono D.path
    Quiver.Path.nil (by simp)

/-- Vanishing of the distinguished coordinate propagates along every prefix
of the literal string through the detector's direct-image/preimage transport. -/
theorem signedPathSubspace_apply_prefixPosition_eq_zero
    (D : Word R) (hmono : IsMonomial R) :
    ∀ {x : Q} (p : SignedPath D.source x)
      (q : SignedPath x D.target) (hp : D.path = p.comp q)
      (U : Submodule k (D.Space D.source))
      (_hU : ∀ v, v ∈ U → v D.sourcePosition = 0)
      (v : D.Space x),
      v ∈ signedPathSubspace (D.rightModule hmono) p U →
        v (⟨p, q, hp⟩ : D.PositionAt x) = 0 := by
  intro x p
  induction hlength : p.length using Nat.strong_induction_on generalizing x with
  | h n ih =>
      cases p with
      | nil =>
          intro q hp U _hU v hv
          rw [signedPathSubspace_nil] at hv
          have hposition :
              (⟨Quiver.Path.nil, q, hp⟩ : D.PositionAt D.source) =
                D.sourcePosition := by
            apply PositionAt.ext_index
            rfl
          rw [hposition]
          exact _hU v hv
      | @cons y _ p e =>
          change Q at y
          intro q hp U _hU v hv
          let previous : D.PositionAt y :=
            ⟨p, e.toPath.comp q, by
              rw [← Quiver.Path.comp_assoc]
              exact hp⟩
          let current : D.PositionAt x := ⟨p.cons e, q, hp⟩
          have hlt : p.length < n := by
            simp only [Quiver.Path.length_cons] at hlength
            omega
          rw [signedPathSubspace_cons] at hv
          cases e with
          | inl a =>
              rcases hv with ⟨w, hw, rfl⟩
              rw [D.moduleArrowMap_rightModule hmono a]
              change D.arrowLinearMap a w current = 0
              rw [D.arrowLinearMap_apply_of_step a w previous current]
              · exact ih p.length hlt p rfl
                  ((positiveArrow a).toPath.comp q) (by
                    rw [← Quiver.Path.comp_assoc]
                    exact hp) U _hU w hw
              · left
                rfl
          | inr a =>
              simp only [signedArrowSubspace] at hv
              rw [D.moduleArrowMap_rightModule hmono a] at hv
              have hprevious := ih p.length hlt p rfl
                ((negativeArrow a).toPath.comp q) (by
                  rw [← Quiver.Path.comp_assoc]
                  exact hp) U _hU (D.arrowLinearMap a v) hv
              rw [D.arrowLinearMap_apply_of_step a v current previous] at hprevious
              · exact hprevious
              · right
                rfl

end Word

variable {A : Type u} [Ring A] [Algebra k A]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : BoundQuiver.StringPresentation k A Q}
variable {S : P.toSpecialBiserialPresentation.ArrowPolarization}
variable {u₀ : Q} {t : Bool}

namespace EndpointWord

@[simp]
theorem signedPathTargetSign_comp_toPath
    {x y z : Q} (p : SignedPath x y) (e : SignedArrow y z) :
    signedPathTargetSign S (p.comp e.toPath) =
      some (signedArrowTargetSign S e) := by
  rw [Quiver.Path.comp_toPath_eq_cons]
  exact signedPathTargetSign_cons S p e

/-- The source-position basis vector of an endpoint word lies in its own
upper boundary filter. -/
theorem sourceBasis_mem_upperBoundarySubspace_rightModule
    (C : EndpointWord S u₀ t) :
    Finsupp.single C.word.sourcePosition (1 : k) ∈
      upperBoundarySubspace (C.word.rightModule P.monomial) C := by
  classical
  by_cases hout : Nonempty C.OutgoingInverseExtension
  · simp only [upperBoundarySubspace, hout, dite_true]
    let out := Classical.choice hout
    change moduleArrowMap (C.word.rightModule P.monomial) out.1.2
      (Finsupp.single C.word.sourcePosition (1 : k)) = 0
    rw [C.word.moduleArrowMap_rightModule P.monomial out.1.2]
    exact C.word.arrowLinearMap_sourceBasis_eq_zero_of_prepend_negative_isString
      out.1.2 out.2.1
  · simp only [upperBoundarySubspace, hout, dite_false]
    trivial

/-- Transporting the upper boundary filter of an endpoint word through its
own literal module contains the target-position basis vector. -/
theorem targetBasis_mem_upperSubspace_rightModule
    (C : EndpointWord S u₀ t) :
    Finsupp.single C.word.targetPosition (1 : k) ∈
      upperSubspace (C.word.rightModule P.monomial) C := by
  have hspan :
      Submodule.span k
          {Finsupp.single C.word.sourcePosition (1 : k)} ≤
        upperBoundarySubspace (C.word.rightModule P.monomial) C := by
    apply Submodule.span_le.mpr
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    exact C.sourceBasis_mem_upperBoundarySubspace_rightModule
  exact (signedPathSubspace_mono (C.word.rightModule P.monomial)
    C.path hspan)
      (C.word.targetBasis_mem_signedPathSubspace_span_source P.monomial)

/-- Every vector in the lower boundary filter of a literal word has zero
source-position coefficient. -/
theorem lowerBoundarySubspace_apply_sourcePosition_eq_zero_rightModule
    (C : EndpointWord S u₀ t) (v : C.word.Space C.word.source)
    (hv : v ∈ lowerBoundarySubspace (C.word.rightModule P.monomial) C) :
    v C.word.sourcePosition = 0 := by
  classical
  by_cases hinc : Nonempty C.IncomingExtension
  · simp only [lowerBoundarySubspace, hinc, dite_true] at hv
    let inc := Classical.choice hinc
    rcases hv with ⟨w, _, rfl⟩
    rw [C.word.moduleArrowMap_rightModule P.monomial inc.1.2]
    exact C.word.arrowLinearMap_apply_sourcePosition_eq_zero_of_prepend_positive_isString
      inc.1.2 w inc.2.1
  · simp only [lowerBoundarySubspace, hinc, dite_false] at hv
    subst v
    rfl

/-- Target-coordinate evaluation vanishes on the complete lower subspace
`C^-` of a literal word evaluated on itself. -/
theorem lowerSubspace_apply_targetPosition_eq_zero_rightModule
    (C : EndpointWord S u₀ t) (v : C.word.Space u₀)
    (hv : v ∈ lowerSubspace (C.word.rightModule P.monomial) C) :
    v C.word.targetPosition = 0 := by
  let final : C.word.PositionAt C.word.target :=
    ⟨C.word.path, Quiver.Path.nil, by simp⟩
  have hfinal : final = C.word.targetPosition := by
    exact Word.PositionAt.ext_index rfl
  rw [← hfinal]
  exact C.word.signedPathSubspace_apply_prefixPosition_eq_zero P.monomial
    C.word.path Quiver.Path.nil (by simp)
      (lowerBoundarySubspace (C.word.rightModule P.monomial) C)
      C.lowerBoundarySubspace_apply_sourcePosition_eq_zero_rightModule v hv

/-- An incoming arrow whose target sign differs from an endpoint word's
target sign cannot hit the word's target-position coordinate. -/
theorem not_exists_arrowStep_to_targetPosition_of_targetSign_ne
    (C : EndpointWord S u₀ t) {x : Q} (a : x ⟶ u₀)
    (hne : S.targetSign a ≠ t) :
    ¬ ∃ i : C.word.PositionAt x,
      C.word.ArrowStep a i C.word.targetPosition := by
  rintro ⟨i, hstep⟩
  rcases hstep with hpositive | hnegative
  · have hsign :
        signedPathTargetSign S C.path = some (S.targetSign a) := by
      change signedPathTargetSign S C.word.path = _
      rw [show C.word.path =
        i.1.comp (positiveArrow a).toPath from hpositive]
      rw [Quiver.Path.comp_toPath_eq_cons]
      rfl
    have htarget := C.targetSign_eq
    unfold signedPathTargetSignOr at htarget
    rw [hsign] at htarget
    exact hne htarget
  · have hlength : i.index = C.word.targetPosition.index + 1 := by
      change i.1.length = C.word.targetPosition.1.length + 1
      rw [hnegative, Quiver.Path.length_comp,
        Quiver.Path.length_toPath]
      rfl
    have hile := i.index_le
    rw [C.word.targetPosition_index] at hlength
    omega

/-- Every image along such an incoming arrow has zero target-position
coefficient. -/
theorem arrowLinearMap_apply_targetPosition_eq_zero_of_targetSign_ne
    (C : EndpointWord S u₀ t) {x : Q} (a : x ⟶ u₀)
    (v : C.word.Space x) (hne : S.targetSign a ≠ t) :
    C.word.arrowLinearMap a v C.word.targetPosition = 0 := by
  exact C.word.arrowLinearMap_apply_eq_zero_of_not_exists_source a v
    C.word.targetPosition
      (C.not_exists_arrowStep_to_targetPosition_of_targetSign_ne a hne)

/-- An outgoing arrow whose source sign differs from an endpoint word's
target sign cannot leave the word's target-position basis vector. -/
theorem not_exists_arrowStep_targetPosition_of_sourceSign_ne
    (C : EndpointWord S u₀ t) {y : Q} (a : u₀ ⟶ y)
    (hne : S.sourceSign a ≠ t) :
    ¬ ∃ j : C.word.PositionAt y,
      C.word.ArrowStep a C.word.targetPosition j := by
  rintro ⟨j, hstep⟩
  rcases hstep with hpositive | hnegative
  · have hlength : j.index = C.word.targetPosition.index + 1 := by
      change j.1.length = C.word.targetPosition.1.length + 1
      rw [hpositive, Quiver.Path.length_comp,
        Quiver.Path.length_toPath]
      rfl
    have hjle := j.index_le
    rw [C.word.targetPosition_index] at hlength
    omega
  · have hsign :
        signedPathTargetSign S C.path = some (S.sourceSign a) := by
      change signedPathTargetSign S C.word.path = _
      rw [show C.word.path =
        j.1.comp (negativeArrow a).toPath from hnegative]
      rw [Quiver.Path.comp_toPath_eq_cons]
      rfl
    have htarget := C.targetSign_eq
    unfold signedPathTargetSignOr at htarget
    rw [hsign] at htarget
    exact hne htarget

/-- Concrete arrow-map form of target-sign exclusion. -/
theorem arrowLinearMap_targetBasis_eq_zero_of_sourceSign_ne
    (C : EndpointWord S u₀ t) {y : Q} (a : u₀ ⟶ y)
    (hne : S.sourceSign a ≠ t) :
    C.word.arrowLinearMap a
        (Finsupp.single C.word.targetPosition (1 : k)) = 0 := by
  rw [C.word.arrowLinearMap_single]
  rw [C.word.arrowOnBasis_eq_zero_of_not_exists a C.word.targetPosition
    (C.not_exists_arrowStep_targetPosition_of_sourceSign_ne a hne)]
  simp

/-- The target-position basis vector lies in the upper boundary filter of
the oppositely polarized trivial word used by the detector. -/
theorem targetBasis_mem_upperBoundarySubspace_oppositeVertex_rightModule
    (C : EndpointWord S u₀ t) :
    Finsupp.single C.word.targetPosition (1 : k) ∈
      upperBoundarySubspace (C.word.rightModule P.monomial)
        C.oppositeVertex := by
  classical
  by_cases hout : Nonempty C.oppositeVertex.OutgoingInverseExtension
  · simp only [upperBoundarySubspace, hout, dite_true]
    let out := Classical.choice hout
    have hne : S.sourceSign out.1.2 ≠ t := by
      intro heq
      have hboundary : t = Bool.not (S.sourceSign out.1.2) := by
        simpa only [oppositeVertex, vertex_sourceSign, Bool.not_not] using
          out.2.2
      rw [heq] at hboundary
      cases t <;> exact Bool.noConfusion hboundary
    change moduleArrowMap (C.word.rightModule P.monomial) out.1.2
      (Finsupp.single C.word.targetPosition (1 : k)) = 0
    rw [C.word.moduleArrowMap_rightModule P.monomial out.1.2]
    exact C.arrowLinearMap_targetBasis_eq_zero_of_sourceSign_ne out.1.2 hne
  · simp only [upperBoundarySubspace, hout, dite_false]
    trivial

/-- Target-coordinate evaluation vanishes on the lower boundary filter of
the oppositely polarized trivial word. -/
theorem lowerBoundarySubspace_oppositeVertex_apply_targetPosition_eq_zero_rightModule
    (C : EndpointWord S u₀ t) (v : C.word.Space u₀)
    (hv : v ∈ lowerBoundarySubspace (C.word.rightModule P.monomial)
      C.oppositeVertex) :
    v C.word.targetPosition = 0 := by
  classical
  by_cases hinc : Nonempty C.oppositeVertex.IncomingExtension
  · simp only [lowerBoundarySubspace, hinc, dite_true] at hv
    let inc := Classical.choice hinc
    have hne : S.targetSign inc.1.2 ≠ t := by
      intro heq
      have hboundary : t = Bool.not (S.targetSign inc.1.2) := by
        simpa only [oppositeVertex, vertex_sourceSign, Bool.not_not] using
          inc.2.2
      rw [heq] at hboundary
      cases t <;> exact Bool.noConfusion hboundary
    rcases hv with ⟨w, _, rfl⟩
    rw [C.word.moduleArrowMap_rightModule P.monomial inc.1.2]
    exact C.arrowLinearMap_apply_targetPosition_eq_zero_of_targetSign_ne
      inc.1.2 w hne
  · simp only [lowerBoundarySubspace, hinc, dite_false] at hv
    subst v
    rfl

/-- Since the opposite trivial word has empty path, its complete lower
subspace also has zero target coordinate. -/
theorem lowerSubspace_oppositeVertex_apply_targetPosition_eq_zero_rightModule
    (C : EndpointWord S u₀ t) (v : C.word.Space u₀)
    (hv : v ∈ lowerSubspace (C.word.rightModule P.monomial)
      C.oppositeVertex) :
    v C.word.targetPosition = 0 := by
  unfold lowerSubspace at hv
  change v ∈ signedPathSubspace (C.word.rightModule P.monomial)
    Quiver.Path.nil
    (lowerBoundarySubspace (C.word.rightModule P.monomial)
      C.oppositeVertex) at hv
  rw [signedPathSubspace_nil] at hv
  exact
    C.lowerBoundarySubspace_oppositeVertex_apply_targetPosition_eq_zero_rightModule
      v hv

/-- The same target vector lies in the complete upper subspace of the
opposite trivial word; its signed path is empty. -/
theorem targetBasis_mem_upperSubspace_oppositeVertex_rightModule
    (C : EndpointWord S u₀ t) :
    Finsupp.single C.word.targetPosition (1 : k) ∈
      upperSubspace (C.word.rightModule P.monomial) C.oppositeVertex := by
  unfold upperSubspace
  change Finsupp.single C.word.targetPosition (1 : k) ∈
    signedPathSubspace (C.word.rightModule P.monomial)
      Quiver.Path.nil
      (upperBoundarySubspace (C.word.rightModule P.monomial)
        C.oppositeVertex)
  rw [signedPathSubspace_nil]
  exact C.targetBasis_mem_upperBoundarySubspace_oppositeVertex_rightModule

/-- The target-position basis vector is a concrete element of the matching
detector numerator `1^+ ∩ C^+`. -/
theorem targetBasis_mem_detectorNumerator_rightModule
    (C : EndpointWord S u₀ t) :
    Finsupp.single C.word.targetPosition (1 : k) ∈
      detectorNumerator (C.word.rightModule P.monomial) C := by
  exact ⟨C.targetBasis_mem_upperSubspace_oppositeVertex_rightModule,
    C.targetBasis_mem_upperSubspace_rightModule⟩

/-- Target-coordinate evaluation annihilates the complete matching detector
denominator. -/
theorem detectorDenominator_apply_targetPosition_eq_zero_rightModule
    (C : EndpointWord S u₀ t) (v : C.word.Space u₀)
    (hv : v ∈ detectorDenominator (C.word.rightModule P.monomial) C) :
    v C.word.targetPosition = 0 := by
  let targetCoordinate :
      (C.word.rightModule P.monomial).obj
          (Opposite.op (BoundQuiver.obj P.toPresentation.relations u₀)) →ₗ[k]
        k :=
    { toFun := fun w ↦
        (show C.word.Space u₀ from w) C.word.targetPosition
      map_add' := by
        intro _ _
        rfl
      map_smul' := by
        intro _ _
        rfl }
  have hdenominator :
      detectorDenominator (C.word.rightModule P.monomial) C ≤
        LinearMap.ker targetCoordinate := by
    unfold detectorDenominator
    apply sup_le
    · intro w hw
      change (show C.word.Space u₀ from w) C.word.targetPosition = 0
      exact C.lowerSubspace_apply_targetPosition_eq_zero_rightModule w hw.2
    · intro w hw
      change (show C.word.Space u₀ from w) C.word.targetPosition = 0
      exact
        C.lowerSubspace_oppositeVertex_apply_targetPosition_eq_zero_rightModule
          w hw.1
  exact hdenominator hv

/-- The distinguished target basis vector is not in the matching detector
denominator. -/
theorem targetBasis_not_mem_detectorDenominator_rightModule
    (C : EndpointWord S u₀ t) :
    Finsupp.single C.word.targetPosition (1 : k) ∉
      detectorDenominator (C.word.rightModule P.monomial) C := by
  intro hmem
  have hzero :=
    C.detectorDenominator_apply_targetPosition_eq_zero_rightModule _ hmem
  have hone :
      (Finsupp.single C.word.targetPosition (1 : k))
          C.word.targetPosition = 1 :=
    Finsupp.single_eq_same
  exact one_ne_zero (hone.symm.trans hzero)

/-- The distinguished numerator element represented by the target-position
basis vector. -/
def targetNumeratorElement (C : EndpointWord S u₀ t) :
    detectorNumerator (C.word.rightModule P.monomial) C :=
  ⟨Finsupp.single C.word.targetPosition (1 : k),
    C.targetBasis_mem_detectorNumerator_rightModule⟩

/-- The distinguished numerator element does not lie in the denominator
viewed as a submodule of the numerator. -/
theorem targetNumeratorElement_not_mem_denominatorInNumerator
    (C : EndpointWord S u₀ t) :
    C.targetNumeratorElement ∉
      detectorDenominatorInNumerator (C.word.rightModule P.monomial) C := by
  exact C.targetBasis_not_mem_detectorDenominator_rightModule

/-- The quotient class of the target-position basis vector in the matching
detector. -/
def targetDetectorClass (C : EndpointWord S u₀ t) :
    DetectorSpace (C.word.rightModule P.monomial) C :=
  Submodule.Quotient.mk C.targetNumeratorElement

/-- The matching detector takes a literal string module to a nonzero vector
space: the target-position class survives its denominator. -/
theorem targetDetectorClass_ne_zero (C : EndpointWord S u₀ t) :
    C.targetDetectorClass ≠ 0 := by
  intro hzero
  apply C.targetNumeratorElement_not_mem_denominatorInNumerator
  exact (Submodule.Quotient.mk_eq_zero _).mp hzero

end EndpointWord

end MagnitudeConjecture.BoundQuiver.StringWord
