import MagnitudeConjecture.Algebra.StringDetectorIndex
import MagnitudeConjecture.Algebra.StringDetectorSelfEvaluation

/-!
# Off-diagonal evaluation of finite-string detectors

A basis coordinate which survives a finite-string detector traces a complete
occurrence of the detector word in the evaluated literal string.  The two
boundary filters make that occurrence maximal at both ends.  It is therefore
the whole evaluated word, in the forward or reverse direction, and detectors
attached to distinct inversion classes vanish.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

variable {P : BoundQuiver.StringPresentation k A Q}
variable {S : P.toSpecialBiserialPresentation.ArrowPolarization}
variable {u₀ : Q} {t : Bool}

namespace Word

/-- A displayed predecessor followed by a realized path segment is itself a
contiguous string segment of the ambient literal word. -/
theorem isString_prepend_of_prefix_eq
    (D : Word P.toPresentation.relations)
    {x y z : Q} (e : SignedArrow x y) (p : SignedPath y z)
    (previous : D.PositionAt x) (first : D.PositionAt y)
    (last : D.PositionAt z)
    (hprevious : first.1 = previous.1.comp e.toPath)
    (hsegment : last.1 = first.1.comp p) :
    IsString P.toPresentation.relations (e.toPath.comp p) := by
  rcases last.2 with ⟨q, hq⟩
  apply IsString.of_contiguousSubpath P.toPresentation.relations D.isString
  refine ⟨previous.1, q, ?_⟩
  calc
    D.path = last.1.comp q := hq
    _ = (first.1.comp p).comp q := by rw [hsegment]
    _ = ((previous.1.comp e.toPath).comp p).comp q := by rw [hprevious]
    _ = previous.1.comp ((e.toPath.comp p).comp q) := by
      simp only [Quiver.Path.comp_assoc]

/-- A realized path segment followed by a displayed successor is itself a
contiguous string segment of the ambient literal word. -/
theorem isString_append_of_prefix_eq
    (D : Word P.toPresentation.relations)
    {x y z : Q} (p : SignedPath x y) (e : SignedArrow y z)
    (first : D.PositionAt x) (last : D.PositionAt y)
    (next : D.PositionAt z)
    (hsegment : last.1 = first.1.comp p)
    (hnext : next.1 = last.1.comp e.toPath) :
    IsString P.toPresentation.relations (p.comp e.toPath) := by
  rcases next.2 with ⟨q, hq⟩
  apply IsString.of_contiguousSubpath P.toPresentation.relations D.isString
  refine ⟨first.1, q, ?_⟩
  calc
    D.path = next.1.comp q := hq
    _ = (last.1.comp e.toPath).comp q := by rw [hnext]
    _ = ((first.1.comp p).comp e.toPath).comp q := by rw [hsegment]
    _ = first.1.comp ((p.comp e.toPath).comp q) := by
      simp only [Quiver.Path.comp_assoc]

/-- A forward segment beginning and ending at the two ambient boundary
indices is the whole ambient word. -/
theorem eq_of_full_forward_segment
    (C D : Word P.toPresentation.relations)
    (first : D.PositionAt C.source) (last : D.PositionAt C.target)
    (hsegment : last.1 = first.1.comp C.path)
    (hfirst : first.index = 0) (hlast : last.index = D.length) :
    D = C := by
  have hsource : D.source = C.source := first.1.eq_of_length_zero hfirst
  have htarget : C.target = D.target :=
    last.eq_target_of_index_eq_length hlast
  rcases C with ⟨csource, ctarget, cpath, hcpath⟩
  rcases D with ⟨dsource, dtarget, dpath, hdpath⟩
  change dsource = csource at hsource
  change ctarget = dtarget at htarget
  subst dsource
  subst dtarget
  have hfirstPath : first.1 = Quiver.Path.nil :=
    first.1.eq_nil_of_length_zero hfirst
  rcases last.2 with ⟨q, hq⟩
  have hlength := congrArg Quiver.Path.length hq
  have hqzero : q.length = 0 := by
    change last.1.length = dpath.length at hlast
    simp only [Quiver.Path.length_comp] at hlength
    omega
  have hqnil : q = Quiver.Path.nil := q.eq_nil_of_length_zero hqzero
  subst q
  have hdpath : dpath = last.1 := by simpa using hq
  have hpath : dpath = cpath := by
    calc
      dpath = last.1 := hdpath
      _ = first.1.comp cpath := hsegment
      _ = cpath := by rw [hfirstPath, Quiver.Path.nil_comp]
  exact Word.ext P.toPresentation.relations rfl rfl (heq_of_eq hpath)

/-- A reverse segment beginning and ending at the two ambient boundary
indices is the whole ambient word in the reverse orientation. -/
theorem eq_reverse_of_full_reverse_segment
    (C D : Word P.toPresentation.relations)
    (first : D.PositionAt C.target) (last : D.PositionAt C.source)
    (hsegment : last.1 = first.1.comp C.path.reverse)
    (hfirst : first.index = 0) (hlast : last.index = D.length) :
    D = C.reverse := by
  have hsource : D.source = C.target := first.1.eq_of_length_zero hfirst
  have htarget : C.source = D.target :=
    last.eq_target_of_index_eq_length hlast
  rcases C with ⟨csource, ctarget, cpath, hcpath⟩
  rcases D with ⟨dsource, dtarget, dpath, hdpath⟩
  change dsource = ctarget at hsource
  change csource = dtarget at htarget
  subst dsource
  subst dtarget
  have hfirstPath : first.1 = Quiver.Path.nil :=
    first.1.eq_nil_of_length_zero hfirst
  rcases last.2 with ⟨q, hq⟩
  have hlength := congrArg Quiver.Path.length hq
  have hqzero : q.length = 0 := by
    change last.1.length = dpath.length at hlast
    simp only [Quiver.Path.length_comp] at hlength
    omega
  have hqnil : q = Quiver.Path.nil := q.eq_nil_of_length_zero hqzero
  subst q
  have hdpath : dpath = last.1 := by simpa using hq
  have hpath : dpath = cpath.reverse := by
    calc
      dpath = last.1 := hdpath
      _ = first.1.comp cpath.reverse := hsegment
      _ = cpath.reverse := by rw [hfirstPath, Quiver.Path.nil_comp]
  exact Word.ext P.toPresentation.relations rfl rfl (heq_of_eq hpath)

end Word

namespace EndpointWord

/-- An endpoint word of length zero is the corresponding formal polarized
vertex word. -/
theorem eq_vertex_of_path_length_eq_zero
    (C : EndpointWord S u₀ t) (hC : C.path.length = 0) :
    C = EndpointWord.vertex P.toSpecialBiserialPresentation S u₀ t := by
  rcases C with ⟨source, path, hstring, htarget⟩
  dsimp at hC
  have hsource : source = u₀ := path.eq_of_length_zero hC
  subst source
  have hpath : path = Quiver.Path.nil := path.eq_nil_of_length_zero hC
  subst path
  rfl

/-- An actual incoming step selected by the lower boundary puts its target
basis vector in that boundary image. -/
theorem single_mem_lowerBoundarySubspace_of_incomingExtension_step
    (D : Word P.toPresentation.relations) (C : EndpointWord S u₀ t)
    (inc : C.IncomingExtension)
    (i : D.PositionAt inc.1.1) (j : D.PositionAt C.source)
    (hstep : D.ArrowStep inc.1.2 i j) :
    Finsupp.single j (1 : k) ∈
      lowerBoundarySubspace (D.rightModule P.monomial) C := by
  classical
  let hinc : Nonempty C.IncomingExtension := ⟨inc⟩
  have hchosen : Classical.choice hinc = inc :=
    @Subsingleton.elim _ C.incomingExtension_subsingleton _ _
  simp only [lowerBoundarySubspace, hinc, dite_true]
  rw [hchosen]
  refine ⟨Finsupp.single i (1 : k), trivial, ?_⟩
  rw [D.moduleArrowMap_rightModule P.monomial inc.1.2]
  exact D.arrowLinearMap_single_one_of_step inc.1.2 i j hstep

/-- An actual outgoing step selected by the upper boundary prevents its
source basis vector from lying in that boundary kernel. -/
theorem single_not_mem_upperBoundarySubspace_of_outgoingInverseExtension_step
    (D : Word P.toPresentation.relations) (C : EndpointWord S u₀ t)
    (out : C.OutgoingInverseExtension)
    (i : D.PositionAt C.source) (j : D.PositionAt out.1.1)
    (hstep : D.ArrowStep out.1.2 i j) :
    Finsupp.single i (1 : k) ∉
      upperBoundarySubspace (D.rightModule P.monomial) C := by
  classical
  let hout : Nonempty C.OutgoingInverseExtension := ⟨out⟩
  have hchosen : Classical.choice hout = out :=
    @Subsingleton.elim _ C.outgoingInverseExtension_subsingleton _ _
  simp only [upperBoundarySubspace, hout, dite_true]
  rw [hchosen]
  change moduleArrowMap (D.rightModule P.monomial) out.1.2
      (Finsupp.single i (1 : k)) ≠ 0
  intro hzero
  have hmap : moduleArrowMap (D.rightModule P.monomial) out.1.2
      (Finsupp.single i (1 : k)) = Finsupp.single j (1 : k) := by
    rw [D.moduleArrowMap_rightModule P.monomial out.1.2]
    exact D.arrowLinearMap_single_one_of_step out.1.2 i j hstep
  rw [hmap] at hzero
  exact (Finsupp.single_ne_zero).2 one_ne_zero hzero

/-- At the forward start of a nonempty occurrence, surviving the lower and
upper source-boundary filters forces the occurrence to begin at index zero of
the ambient literal string. -/
theorem forwardOccurrence_sourceIndex_eq_zero
    (D : Word P.toPresentation.relations) (C : EndpointWord S u₀ t)
    (hC : 0 < C.path.length)
    (first : D.PositionAt C.source) (last : D.PositionAt u₀)
    (hsegment : last.1 = first.1.comp C.path)
    (hupper : Finsupp.single first (1 : k) ∈
      upperBoundarySubspace (D.rightModule P.monomial) C)
    (hnotLower : Finsupp.single first (1 : k) ∉
      lowerBoundarySubspace (D.rightModule P.monomial) C) :
    first.index = 0 := by
  by_contra hne
  have hpos : 0 < first.index := Nat.pos_of_ne_zero hne
  rcases D.exists_arrowStep_of_index_pos ⟨C.source, first⟩ hpos with
    hpositive | hnegative
  · rcases hpositive with ⟨x, previous, a, hindex, hstep⟩
    have hprefix : first.1 =
        previous.1.comp (positiveArrow a).toPath := by
      rcases hstep with hforward | hbackward
      · exact hforward
      · have hlength := congrArg Quiver.Path.length hbackward
        simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
          at hlength
        change previous.index + 1 = first.index at hindex
        change previous.index = first.index + 1 at hlength
        omega
    have hstring := D.isString_prepend_of_prefix_eq
      (positiveArrow a) C.path previous first last hprefix hsegment
    have hsourceOption :=
      signedPathSourceSign_eq_not_targetSign_of_isString_prepend S
        (positiveArrow a) C.path hC hstring
    have hsource : C.sourceSign = Bool.not (S.targetSign a) := by
      unfold EndpointWord.sourceSign signedPathSourceSignOr
      rw [hsourceOption]
      rfl
    let inc : C.IncomingExtension :=
      ⟨⟨x, a⟩, hstring, hsource⟩
    exact hnotLower
      (C.single_mem_lowerBoundarySubspace_of_incomingExtension_step
        D inc previous first hstep)
  · rcases hnegative with ⟨x, previous, a, hindex, hstep⟩
    have hprefix : first.1 =
        previous.1.comp (negativeArrow a).toPath := by
      rcases hstep with hforward | hbackward
      · have hlength := congrArg Quiver.Path.length hforward
        simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
          at hlength
        change previous.index + 1 = first.index at hindex
        change previous.index = first.index + 1 at hlength
        omega
      · exact hbackward
    have hstring := D.isString_prepend_of_prefix_eq
      (negativeArrow a) C.path previous first last hprefix hsegment
    have hsourceOption :=
      signedPathSourceSign_eq_not_targetSign_of_isString_prepend S
        (negativeArrow a) C.path hC hstring
    have hsource : C.sourceSign = Bool.not (S.sourceSign a) := by
      unfold EndpointWord.sourceSign signedPathSourceSignOr
      rw [hsourceOption]
      rfl
    let out : C.OutgoingInverseExtension :=
      ⟨⟨x, a⟩, hstring, hsource⟩
    exact
      (C.single_not_mem_upperBoundarySubspace_of_outgoingInverseExtension_step
        D out first previous hstep) hupper

/-- At the forward end of a nonempty occurrence, the opposite trivial
boundary filters force the occurrence to end at the final ambient index. -/
theorem forwardOccurrence_targetIndex_eq_length
    (D : Word P.toPresentation.relations) (C : EndpointWord S u₀ t)
    (hC : 0 < C.path.length)
    (first : D.PositionAt C.source) (last : D.PositionAt u₀)
    (hsegment : last.1 = first.1.comp C.path)
    (hupper : Finsupp.single last (1 : k) ∈
      upperBoundarySubspace (D.rightModule P.monomial) C.oppositeVertex)
    (hnotLower : Finsupp.single last (1 : k) ∉
      lowerBoundarySubspace (D.rightModule P.monomial) C.oppositeVertex) :
    last.index = D.length := by
  by_contra hne
  have hlt : last.index < D.length :=
    Nat.lt_of_le_of_ne last.index_le hne
  rcases D.exists_arrowStep_of_index_lt_length ⟨u₀, last⟩ hlt with
    hpositive | hnegative
  · rcases hpositive with ⟨z, next, a, hindex, hstep⟩
    have hprefix : next.1 = last.1.comp (positiveArrow a).toPath := by
      rcases hstep with hforward | hbackward
      · exact hforward
      · have hlength := congrArg Quiver.Path.length hbackward
        simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
          at hlength
        change next.index = last.index + 1 at hindex
        change last.index = next.index + 1 at hlength
        omega
    have hstring := D.isString_append_of_prefix_eq
      C.path (positiveArrow a) first last next hsegment hprefix
    have htargetOption :=
      signedPathTargetSign_eq_not_sourceSign_of_isString_append S
        C.path (positiveArrow a) hC hstring
    have htarget : t = Bool.not (S.sourceSign a) := by
      have h := C.targetSign_eq
      unfold signedPathTargetSignOr at h
      rw [htargetOption] at h
      exact h.symm
    have hoppositeSource : C.oppositeVertex.sourceSign =
        Bool.not (S.sourceSign a) := by
      simpa only [oppositeVertex, vertex_sourceSign, Bool.not_not] using htarget
    have hsingle : IsString P.toPresentation.relations
        ((negativeArrow a).toPath.comp C.oppositeVertex.path) := by
      apply isString_of_length_lt_two P.toPresentation.relations
        P.toPresentation.admissible
      simp [oppositeVertex, EndpointWord.vertex]
    let out : C.oppositeVertex.OutgoingInverseExtension :=
      ⟨⟨z, a⟩, hsingle, hoppositeSource⟩
    exact
      (C.oppositeVertex.single_not_mem_upperBoundarySubspace_of_outgoingInverseExtension_step
        D out last next hstep) hupper
  · rcases hnegative with ⟨z, next, a, hindex, hstep⟩
    have hprefix : next.1 = last.1.comp (negativeArrow a).toPath := by
      rcases hstep with hforward | hbackward
      · have hlength := congrArg Quiver.Path.length hforward
        simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
          at hlength
        change next.index = last.index + 1 at hindex
        change last.index = next.index + 1 at hlength
        omega
      · exact hbackward
    have hstring := D.isString_append_of_prefix_eq
      C.path (negativeArrow a) first last next hsegment hprefix
    have htargetOption :=
      signedPathTargetSign_eq_not_sourceSign_of_isString_append S
        C.path (negativeArrow a) hC hstring
    have htarget : t = Bool.not (S.targetSign a) := by
      have h := C.targetSign_eq
      unfold signedPathTargetSignOr at h
      rw [htargetOption] at h
      exact h.symm
    have hoppositeSource : C.oppositeVertex.sourceSign =
        Bool.not (S.targetSign a) := by
      simpa only [oppositeVertex, vertex_sourceSign, Bool.not_not] using htarget
    have hsingle : IsString P.toPresentation.relations
        ((positiveArrow a).toPath.comp C.oppositeVertex.path) := by
      apply isString_of_length_lt_two P.toPresentation.relations
        P.toPresentation.admissible
      simp [oppositeVertex, EndpointWord.vertex]
    let inc : C.oppositeVertex.IncomingExtension :=
      ⟨⟨z, a⟩, hsingle, hoppositeSource⟩
    exact hnotLower
      (C.oppositeVertex.single_mem_lowerBoundarySubspace_of_incomingExtension_step
        D inc next last hstep)

/-- At the start of a reverse occurrence, the opposite trivial boundary
filters force the occurrence to begin at the initial ambient index. -/
theorem reverseOccurrence_targetIndex_eq_zero
    (D : Word P.toPresentation.relations) (C : EndpointWord S u₀ t)
    (hC : 0 < C.path.length)
    (first : D.PositionAt u₀) (last : D.PositionAt C.source)
    (hsegment : last.1 = first.1.comp C.path.reverse)
    (hupper : Finsupp.single first (1 : k) ∈
      upperBoundarySubspace (D.rightModule P.monomial) C.oppositeVertex)
    (hnotLower : Finsupp.single first (1 : k) ∉
      lowerBoundarySubspace (D.rightModule P.monomial) C.oppositeVertex) :
    first.index = 0 := by
  by_contra hne
  have hpos : 0 < first.index := Nat.pos_of_ne_zero hne
  rcases D.exists_arrowStep_of_index_pos ⟨u₀, first⟩ hpos with
    hpositive | hnegative
  · rcases hpositive with ⟨x, previous, a, hindex, hstep⟩
    have hprefix : first.1 =
        previous.1.comp (positiveArrow a).toPath := by
      rcases hstep with hforward | hbackward
      · exact hforward
      · have hlength := congrArg Quiver.Path.length hbackward
        simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
          at hlength
        change previous.index + 1 = first.index at hindex
        change previous.index = first.index + 1 at hlength
        omega
    have hstring := D.isString_prepend_of_prefix_eq
      (positiveArrow a) C.path.reverse previous first last hprefix hsegment
    have hsourceOption :=
      signedPathSourceSign_eq_not_targetSign_of_isString_prepend S
        (positiveArrow a) C.path.reverse (by
          rw [length_reverse]
          exact hC) hstring
    have htarget : t = Bool.not (S.targetSign a) := by
      rw [signedPathSourceSign_reverse] at hsourceOption
      have h := C.targetSign_eq
      unfold signedPathTargetSignOr at h
      rw [hsourceOption] at h
      exact h.symm
    have hoppositeSource : C.oppositeVertex.sourceSign =
        Bool.not (S.targetSign a) := by
      simpa only [oppositeVertex, vertex_sourceSign, Bool.not_not] using htarget
    have hsingle : IsString P.toPresentation.relations
        ((positiveArrow a).toPath.comp C.oppositeVertex.path) := by
      apply isString_of_length_lt_two P.toPresentation.relations
        P.toPresentation.admissible
      simp [oppositeVertex, EndpointWord.vertex]
    let inc : C.oppositeVertex.IncomingExtension :=
      ⟨⟨x, a⟩, hsingle, hoppositeSource⟩
    exact hnotLower
      (C.oppositeVertex.single_mem_lowerBoundarySubspace_of_incomingExtension_step
        D inc previous first hstep)
  · rcases hnegative with ⟨x, previous, a, hindex, hstep⟩
    have hprefix : first.1 =
        previous.1.comp (negativeArrow a).toPath := by
      rcases hstep with hforward | hbackward
      · have hlength := congrArg Quiver.Path.length hforward
        simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
          at hlength
        change previous.index + 1 = first.index at hindex
        change previous.index = first.index + 1 at hlength
        omega
      · exact hbackward
    have hstring := D.isString_prepend_of_prefix_eq
      (negativeArrow a) C.path.reverse previous first last hprefix hsegment
    have hsourceOption :=
      signedPathSourceSign_eq_not_targetSign_of_isString_prepend S
        (negativeArrow a) C.path.reverse (by
          rw [length_reverse]
          exact hC) hstring
    have htarget : t = Bool.not (S.sourceSign a) := by
      rw [signedPathSourceSign_reverse] at hsourceOption
      have h := C.targetSign_eq
      unfold signedPathTargetSignOr at h
      rw [hsourceOption] at h
      exact h.symm
    have hoppositeSource : C.oppositeVertex.sourceSign =
        Bool.not (S.sourceSign a) := by
      simpa only [oppositeVertex, vertex_sourceSign, Bool.not_not] using htarget
    have hsingle : IsString P.toPresentation.relations
        ((negativeArrow a).toPath.comp C.oppositeVertex.path) := by
      apply isString_of_length_lt_two P.toPresentation.relations
        P.toPresentation.admissible
      simp [oppositeVertex, EndpointWord.vertex]
    let out : C.oppositeVertex.OutgoingInverseExtension :=
      ⟨⟨x, a⟩, hsingle, hoppositeSource⟩
    exact
      (C.oppositeVertex.single_not_mem_upperBoundarySubspace_of_outgoingInverseExtension_step
        D out first previous hstep) hupper

/-- At the end of a reverse occurrence, the source-boundary filters of the
original endpoint word force the occurrence to end at the final ambient
index. -/
theorem reverseOccurrence_sourceIndex_eq_length
    (D : Word P.toPresentation.relations) (C : EndpointWord S u₀ t)
    (hC : 0 < C.path.length)
    (first : D.PositionAt u₀) (last : D.PositionAt C.source)
    (hsegment : last.1 = first.1.comp C.path.reverse)
    (hupper : Finsupp.single last (1 : k) ∈
      upperBoundarySubspace (D.rightModule P.monomial) C)
    (hnotLower : Finsupp.single last (1 : k) ∉
      lowerBoundarySubspace (D.rightModule P.monomial) C) :
    last.index = D.length := by
  by_contra hne
  have hlt : last.index < D.length :=
    Nat.lt_of_le_of_ne last.index_le hne
  rcases D.exists_arrowStep_of_index_lt_length ⟨C.source, last⟩ hlt with
    hpositive | hnegative
  · rcases hpositive with ⟨z, next, a, hindex, hstep⟩
    have hprefix : next.1 = last.1.comp (positiveArrow a).toPath := by
      rcases hstep with hforward | hbackward
      · exact hforward
      · have hlength := congrArg Quiver.Path.length hbackward
        simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
          at hlength
        change next.index = last.index + 1 at hindex
        change last.index = next.index + 1 at hlength
        omega
    have hstring := D.isString_append_of_prefix_eq
      C.path.reverse (positiveArrow a) first last next hsegment hprefix
    have htargetOption :=
      signedPathTargetSign_eq_not_sourceSign_of_isString_append S
        C.path.reverse (positiveArrow a) (by
          rw [length_reverse]
          exact hC) hstring
    have hsource : C.sourceSign = Bool.not (S.sourceSign a) := by
      rw [signedPathTargetSign_reverse] at htargetOption
      unfold EndpointWord.sourceSign signedPathSourceSignOr
      rw [htargetOption]
      rfl
    have hrequired : IsString P.toPresentation.relations
        ((negativeArrow a).toPath.comp C.path) := by
      have hreverse :=
        (isString_reverse_iff P.toPresentation.relations _).2 hstring
      simpa only [Quiver.Path.reverse_comp,
        Quiver.Path.reverse_toPath, reverse_positiveArrow,
        Quiver.Path.reverse_reverse] using hreverse
    let out : C.OutgoingInverseExtension :=
      ⟨⟨z, a⟩, hrequired, hsource⟩
    exact
      (C.single_not_mem_upperBoundarySubspace_of_outgoingInverseExtension_step
        D out last next hstep) hupper
  · rcases hnegative with ⟨z, next, a, hindex, hstep⟩
    have hprefix : next.1 = last.1.comp (negativeArrow a).toPath := by
      rcases hstep with hforward | hbackward
      · have hlength := congrArg Quiver.Path.length hforward
        simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
          at hlength
        change next.index = last.index + 1 at hindex
        change last.index = next.index + 1 at hlength
        omega
      · exact hbackward
    have hstring := D.isString_append_of_prefix_eq
      C.path.reverse (negativeArrow a) first last next hsegment hprefix
    have htargetOption :=
      signedPathTargetSign_eq_not_sourceSign_of_isString_append S
        C.path.reverse (negativeArrow a) (by
          rw [length_reverse]
          exact hC) hstring
    have hsource : C.sourceSign = Bool.not (S.targetSign a) := by
      rw [signedPathTargetSign_reverse] at htargetOption
      unfold EndpointWord.sourceSign signedPathSourceSignOr
      rw [htargetOption]
      rfl
    have hrequired : IsString P.toPresentation.relations
        ((positiveArrow a).toPath.comp C.path) := by
      have hreverse :=
        (isString_reverse_iff P.toPresentation.relations _).2 hstring
      simpa only [Quiver.Path.reverse_comp,
        Quiver.Path.reverse_toPath, reverse_negativeArrow,
        Quiver.Path.reverse_reverse] using hreverse
    let inc : C.IncomingExtension :=
      ⟨⟨z, a⟩, hrequired, hsource⟩
    exact hnotLower
      (C.single_mem_lowerBoundarySubspace_of_incomingExtension_step
        D inc next last hstep)

/-- For a formal vertex word and its opposite polarization, surviving both
upper filters and neither lower filter forces the selected position to be the
initial position of the ambient word. -/
theorem trivialPair_index_eq_zero
    (D : Word P.toPresentation.relations) (u : Q) (s : Bool)
    (i : D.PositionAt u)
    (hupper : Finsupp.single i (1 : k) ∈
      upperBoundarySubspace (D.rightModule P.monomial)
        (EndpointWord.vertex P.toSpecialBiserialPresentation S u s))
    (hupperOpposite : Finsupp.single i (1 : k) ∈
      upperBoundarySubspace (D.rightModule P.monomial)
        (EndpointWord.vertex P.toSpecialBiserialPresentation S u (Bool.not s)))
    (hnotLower : Finsupp.single i (1 : k) ∉
      lowerBoundarySubspace (D.rightModule P.monomial)
        (EndpointWord.vertex P.toSpecialBiserialPresentation S u s))
    (hnotLowerOpposite : Finsupp.single i (1 : k) ∉
      lowerBoundarySubspace (D.rightModule P.monomial)
        (EndpointWord.vertex P.toSpecialBiserialPresentation S u (Bool.not s))) :
    i.index = 0 := by
  let V := EndpointWord.vertex P.toSpecialBiserialPresentation S u s
  let W := EndpointWord.vertex P.toSpecialBiserialPresentation S u (Bool.not s)
  by_contra hne
  have hpos : 0 < i.index := Nat.pos_of_ne_zero hne
  rcases D.exists_arrowStep_of_index_pos ⟨u, i⟩ hpos with
    hpositive | hnegative
  · rcases hpositive with ⟨x, previous, a, _, hstep⟩
    have hsingleV : IsString P.toPresentation.relations
        ((positiveArrow a).toPath.comp V.path) := by
      apply isString_of_length_lt_two P.toPresentation.relations
        P.toPresentation.admissible
      simp [V, EndpointWord.vertex]
    by_cases hsign : V.sourceSign = Bool.not (S.targetSign a)
    · let inc : V.IncomingExtension := ⟨⟨x, a⟩, hsingleV, hsign⟩
      exact hnotLower
        (V.single_mem_lowerBoundarySubspace_of_incomingExtension_step
          D inc previous i hstep)
    · have hoppositeSign : W.sourceSign =
          Bool.not (S.targetSign a) := by
        simp only [V, W, vertex_sourceSign, Bool.not_not] at hsign ⊢
        rw [Bool.eq_not_iff]
        intro heq
        apply hsign
        rw [heq]
      have hsingleW : IsString P.toPresentation.relations
          ((positiveArrow a).toPath.comp W.path) := by
        apply isString_of_length_lt_two P.toPresentation.relations
          P.toPresentation.admissible
        simp [W, EndpointWord.vertex]
      let inc : W.IncomingExtension :=
        ⟨⟨x, a⟩, hsingleW, hoppositeSign⟩
      exact hnotLowerOpposite
        (W.single_mem_lowerBoundarySubspace_of_incomingExtension_step
          D inc previous i hstep)
  · rcases hnegative with ⟨x, previous, a, _, hstep⟩
    have hsingleV : IsString P.toPresentation.relations
        ((negativeArrow a).toPath.comp V.path) := by
      apply isString_of_length_lt_two P.toPresentation.relations
        P.toPresentation.admissible
      simp [V, EndpointWord.vertex]
    by_cases hsign : V.sourceSign = Bool.not (S.sourceSign a)
    · let out : V.OutgoingInverseExtension := ⟨⟨x, a⟩, hsingleV, hsign⟩
      exact
        (V.single_not_mem_upperBoundarySubspace_of_outgoingInverseExtension_step
          D out i previous hstep) hupper
    · have hoppositeSign : W.sourceSign =
          Bool.not (S.sourceSign a) := by
        simp only [V, W, vertex_sourceSign, Bool.not_not] at hsign ⊢
        rw [Bool.eq_not_iff]
        intro heq
        apply hsign
        rw [heq]
      have hsingleW : IsString P.toPresentation.relations
          ((negativeArrow a).toPath.comp W.path) := by
        apply isString_of_length_lt_two P.toPresentation.relations
          P.toPresentation.admissible
        simp [W, EndpointWord.vertex]
      let out : W.OutgoingInverseExtension :=
        ⟨⟨x, a⟩, hsingleW, hoppositeSign⟩
      exact
        (W.single_not_mem_upperBoundarySubspace_of_outgoingInverseExtension_step
          D out i previous hstep) hupperOpposite

/-- The same two polarized trivial filters force a surviving position to be
the final position of the ambient word. -/
theorem trivialPair_index_eq_length
    (D : Word P.toPresentation.relations) (u : Q) (s : Bool)
    (i : D.PositionAt u)
    (hupper : Finsupp.single i (1 : k) ∈
      upperBoundarySubspace (D.rightModule P.monomial)
        (EndpointWord.vertex P.toSpecialBiserialPresentation S u s))
    (hupperOpposite : Finsupp.single i (1 : k) ∈
      upperBoundarySubspace (D.rightModule P.monomial)
        (EndpointWord.vertex P.toSpecialBiserialPresentation S u (Bool.not s)))
    (hnotLower : Finsupp.single i (1 : k) ∉
      lowerBoundarySubspace (D.rightModule P.monomial)
        (EndpointWord.vertex P.toSpecialBiserialPresentation S u s))
    (hnotLowerOpposite : Finsupp.single i (1 : k) ∉
      lowerBoundarySubspace (D.rightModule P.monomial)
        (EndpointWord.vertex P.toSpecialBiserialPresentation S u (Bool.not s))) :
    i.index = D.length := by
  let V := EndpointWord.vertex P.toSpecialBiserialPresentation S u s
  let W := EndpointWord.vertex P.toSpecialBiserialPresentation S u (Bool.not s)
  by_contra hne
  have hlt : i.index < D.length := Nat.lt_of_le_of_ne i.index_le hne
  rcases D.exists_arrowStep_of_index_lt_length ⟨u, i⟩ hlt with
    hpositive | hnegative
  · rcases hpositive with ⟨z, next, a, _, hstep⟩
    have hsingleV : IsString P.toPresentation.relations
        ((negativeArrow a).toPath.comp V.path) := by
      apply isString_of_length_lt_two P.toPresentation.relations
        P.toPresentation.admissible
      simp [V, EndpointWord.vertex]
    by_cases hsign : V.sourceSign = Bool.not (S.sourceSign a)
    · let out : V.OutgoingInverseExtension := ⟨⟨z, a⟩, hsingleV, hsign⟩
      exact
        (V.single_not_mem_upperBoundarySubspace_of_outgoingInverseExtension_step
          D out i next hstep) hupper
    · have hoppositeSign : W.sourceSign =
          Bool.not (S.sourceSign a) := by
        simp only [V, W, vertex_sourceSign, Bool.not_not] at hsign ⊢
        rw [Bool.eq_not_iff]
        intro heq
        apply hsign
        rw [heq]
      have hsingleW : IsString P.toPresentation.relations
          ((negativeArrow a).toPath.comp W.path) := by
        apply isString_of_length_lt_two P.toPresentation.relations
          P.toPresentation.admissible
        simp [W, EndpointWord.vertex]
      let out : W.OutgoingInverseExtension :=
        ⟨⟨z, a⟩, hsingleW, hoppositeSign⟩
      exact
        (W.single_not_mem_upperBoundarySubspace_of_outgoingInverseExtension_step
          D out i next hstep) hupperOpposite
  · rcases hnegative with ⟨z, next, a, _, hstep⟩
    have hsingleV : IsString P.toPresentation.relations
        ((positiveArrow a).toPath.comp V.path) := by
      apply isString_of_length_lt_two P.toPresentation.relations
        P.toPresentation.admissible
      simp [V, EndpointWord.vertex]
    by_cases hsign : V.sourceSign = Bool.not (S.targetSign a)
    · let inc : V.IncomingExtension := ⟨⟨z, a⟩, hsingleV, hsign⟩
      exact hnotLower
        (V.single_mem_lowerBoundarySubspace_of_incomingExtension_step
          D inc next i hstep)
    · have hoppositeSign : W.sourceSign =
          Bool.not (S.targetSign a) := by
        simp only [V, W, vertex_sourceSign, Bool.not_not] at hsign ⊢
        rw [Bool.eq_not_iff]
        intro heq
        apply hsign
        rw [heq]
      have hsingleW : IsString P.toPresentation.relations
          ((positiveArrow a).toPath.comp W.path) := by
        apply isString_of_length_lt_two P.toPresentation.relations
          P.toPresentation.admissible
        simp [W, EndpointWord.vertex]
      let inc : W.IncomingExtension :=
        ⟨⟨z, a⟩, hsingleW, hoppositeSign⟩
      exact hnotLowerOpposite
        (W.single_mem_lowerBoundarySubspace_of_incomingExtension_step
          D inc next i hstep)

/-- If one position basis vector survives the detector indexed by `C` on a
literal string module `M(D)`, then `D` is the word of `C` or its formal
reverse. -/
theorem word_eq_or_eq_reverse_of_single_mem_detectorNumerator_not_denominator
    (C : EndpointWord S u₀ t)
    (D : Word P.toPresentation.relations) (i : D.PositionAt u₀)
    (hnum : Finsupp.single i (1 : k) ∈
      detectorNumerator (D.rightModule P.monomial) C)
    (hnotDen : Finsupp.single i (1 : k) ∉
      detectorDenominator (D.rightModule P.monomial) C) :
    C.word = D ∨ C.word = D.reverse := by
  change Finsupp.single i (1 : k) ∈
      upperSubspace (D.rightModule P.monomial) C.oppositeVertex ⊓
        upperSubspace (D.rightModule P.monomial) C at hnum
  have hiUpperOpposite := hnum.1
  have hiUpper := hnum.2
  have hiNotLower : Finsupp.single i (1 : k) ∉
      lowerSubspace (D.rightModule P.monomial) C := by
    intro hlower
    apply hnotDen
    exact (le_sup_left :
      upperSubspace (D.rightModule P.monomial) C.oppositeVertex ⊓
          lowerSubspace (D.rightModule P.monomial) C ≤
        detectorDenominator (D.rightModule P.monomial) C)
      ⟨hiUpperOpposite, hlower⟩
  have hiNotLowerOpposite : Finsupp.single i (1 : k) ∉
      lowerSubspace (D.rightModule P.monomial) C.oppositeVertex := by
    intro hlower
    apply hnotDen
    exact (le_sup_right :
      lowerSubspace (D.rightModule P.monomial) C.oppositeVertex ⊓
          upperSubspace (D.rightModule P.monomial) C ≤
        detectorDenominator (D.rightModule P.monomial) C)
      ⟨hlower, hiUpper⟩
  have hiUpperOppositeBoundary : Finsupp.single i (1 : k) ∈
      upperBoundarySubspace (D.rightModule P.monomial) C.oppositeVertex := by
    rw [upperSubspace_oppositeVertex] at hiUpperOpposite
    exact hiUpperOpposite
  have hiNotLowerOppositeBoundary : Finsupp.single i (1 : k) ∉
      lowerBoundarySubspace (D.rightModule P.monomial) C.oppositeVertex := by
    rw [lowerSubspace_oppositeVertex] at hiNotLowerOpposite
    exact hiNotLowerOpposite
  rcases D.exists_positionReach_of_single_mem_signedPathSubspace_not_mem
      P.monomial C.path
      (C.upperBoundarySubspace_isCoordinate_rightModule D)
      i hiUpper hiNotLower with
    ⟨j, hreach, hjUpperBoundary, hjNotLowerBoundary⟩
  by_cases hCpos : 0 < C.path.length
  · rcases C.word.positionReach_endpointSlope D hreach with
      hforward | hreverse
    · have hsegment := D.positionReach_prefix_eq_of_forward
        C.path C.isString j i hreach hforward
      have hjzero := C.forwardOccurrence_sourceIndex_eq_zero
        D hCpos j i hsegment hjUpperBoundary hjNotLowerBoundary
      have hilength := C.forwardOccurrence_targetIndex_eq_length
        D hCpos j i hsegment hiUpperOppositeBoundary
          hiNotLowerOppositeBoundary
      exact Or.inl
        (C.word.eq_of_full_forward_segment D j i hsegment hjzero hilength).symm
    · have hsegment := D.positionReach_prefix_eq_of_reverse
        C.path C.isString j i hreach hreverse
      have hizero := C.reverseOccurrence_targetIndex_eq_zero
        D hCpos i j hsegment hiUpperOppositeBoundary
          hiNotLowerOppositeBoundary
      have hjlength := C.reverseOccurrence_sourceIndex_eq_length
        D hCpos i j hsegment hjUpperBoundary hjNotLowerBoundary
      have hword := C.word.eq_reverse_of_full_reverse_segment
        D i j hsegment hizero hjlength
      right
      have hreverseWord := congrArg
        (fun W : Word P.toPresentation.relations ↦ W.reverse) hword
      simpa using hreverseWord.symm
  · have hCzero : C.path.length = 0 := Nat.eq_zero_of_not_pos hCpos
    have hCvertex := C.eq_vertex_of_path_length_eq_zero hCzero
    cases hCvertex
    have hji : j = i := by
      exact (D.signedPathPositionReach_nil j i).1 hreach
    subst j
    have hizero := trivialPair_index_eq_zero D u₀ t i
      hjUpperBoundary hiUpperOppositeBoundary
      hjNotLowerBoundary hiNotLowerOppositeBoundary
    have hilength := trivialPair_index_eq_length D u₀ t i
      hjUpperBoundary hiUpperOppositeBoundary
      hjNotLowerBoundary hiNotLowerOppositeBoundary
    let V := EndpointWord.vertex P.toSpecialBiserialPresentation S u₀ t
    have hsegment : i.1 = i.1.comp V.path := by
      change i.1 = i.1.comp Quiver.Path.nil
      simp
    have hword : D = V.word := V.word.eq_of_full_forward_segment
      D i i hsegment hizero hilength
    left
    exact hword.symm

/-- Away from the inversion class of `C`, every numerator basis coordinate
already belongs to the detector denominator. -/
theorem single_mem_detectorDenominator_of_not_inverseEquivalent
    (C : EndpointWord S u₀ t)
    (D : Word P.toPresentation.relations)
    (hnot : ¬ (C.word = D ∨ C.word = D.reverse))
    (i : D.PositionAt u₀)
    (hnum : Finsupp.single i (1 : k) ∈
      detectorNumerator (D.rightModule P.monomial) C) :
    Finsupp.single i (1 : k) ∈
      detectorDenominator (D.rightModule P.monomial) C := by
  by_contra hden
  exact hnot
    (C.word_eq_or_eq_reverse_of_single_mem_detectorNumerator_not_denominator
      D i hnum hden)

/-- On a literal string outside the inversion class of `C`, the detector
denominator equals its numerator. -/
theorem detectorDenominator_eq_detectorNumerator_of_not_inverseEquivalent
    (C : EndpointWord S u₀ t)
    (D : Word P.toPresentation.relations)
    (hnot : ¬ (C.word = D ∨ C.word = D.reverse)) :
    detectorDenominator (D.rightModule P.monomial) C =
      detectorNumerator (D.rightModule P.monomial) C := by
  apply le_antisymm
  · exact detectorDenominator_le_detectorNumerator
      (D.rightModule P.monomial) C
  · intro v hv
    let w : D.Space u₀ := v
    change w ∈ detectorNumerator (D.rightModule P.monomial) C at hv
    change w ∈ detectorDenominator (D.rightModule P.monomial) C
    have hparts : ∀ i : D.PositionAt u₀,
        Finsupp.single i (w i) ∈
          detectorDenominator (D.rightModule P.monomial) C := by
      intro i
      by_cases hcoefficient : w i = 0
      · rw [hcoefficient, Finsupp.single_zero]
        change (0 : (D.rightModule P.monomial).obj
          (Opposite.op (BoundQuiver.obj P.toPresentation.relations u₀))) ∈
            detectorDenominator (D.rightModule P.monomial) C
        exact (detectorDenominator (D.rightModule P.monomial) C).zero_mem
      · have hpartNumerator : Finsupp.single i (w i) ∈
            detectorNumerator (D.rightModule P.monomial) C :=
          C.detectorNumerator_isCoordinate_rightModule D w hv i
        have honeNumerator : Finsupp.single i (1 : k) ∈
            detectorNumerator (D.rightModule P.monomial) C := by
          have hscaled :=
            (detectorNumerator (D.rightModule P.monomial) C).smul_mem
              (w i)⁻¹ hpartNumerator
          have heq : (w i)⁻¹ • Finsupp.single i (w i) =
              Finsupp.single i (1 : k) := by
            rw [Finsupp.smul_single', inv_mul_cancel₀ hcoefficient]
          rw [← heq]
          exact hscaled
        have honeDenominator :=
          C.single_mem_detectorDenominator_of_not_inverseEquivalent
            D hnot i honeNumerator
        have hscaled :=
          (detectorDenominator (D.rightModule P.monomial) C).smul_mem
            (w i) honeDenominator
        rw [← Finsupp.smul_single_one i (w i)]
        exact hscaled
    exact D.mem_of_all_coordinateParts_mem
      (detectorDenominator (D.rightModule P.monomial) C) w hparts

/-- Off the inversion class of `C`, the denominator inside the numerator is
the whole numerator. -/
theorem detectorDenominatorInNumerator_eq_top_of_not_inverseEquivalent
    (C : EndpointWord S u₀ t)
    (D : Word P.toPresentation.relations)
    (hnot : ¬ (C.word = D ∨ C.word = D.reverse)) :
    detectorDenominatorInNumerator (D.rightModule P.monomial) C = ⊤ := by
  apply top_unique
  rintro ⟨v, hv⟩ _
  change v ∈ detectorDenominator (D.rightModule P.monomial) C
  rw [C.detectorDenominator_eq_detectorNumerator_of_not_inverseEquivalent
    D hnot]
  exact hv

/-- Every off-diagonal finite-string detector space is subsingleton. -/
theorem detectorSpace_subsingleton_of_not_inverseEquivalent
    (C : EndpointWord S u₀ t)
    (D : Word P.toPresentation.relations)
    (hnot : ¬ (C.word = D ∨ C.word = D.reverse)) :
    Subsingleton (DetectorSpace (D.rightModule P.monomial) C) := by
  rw [Submodule.Quotient.subsingleton_iff]
  exact C.detectorDenominatorInNumerator_eq_top_of_not_inverseEquivalent
    D hnot

/-- Literal dimension statement for off-diagonal detector evaluation. -/
theorem finrank_detectorSpace_rightModule_eq_zero_of_not_inverseEquivalent
    (C : EndpointWord S u₀ t)
    (D : Word P.toPresentation.relations)
    (hnot : ¬ (C.word = D ∨ C.word = D.reverse)) :
    Module.finrank k (DetectorSpace (D.rightModule P.monomial) C) = 0 := by
  letI : Subsingleton (DetectorSpace (D.rightModule P.monomial) C) :=
    C.detectorSpace_subsingleton_of_not_inverseEquivalent D hnot
  exact Module.finrank_zero_of_subsingleton

end EndpointWord

namespace DetectorIndex

local instance : DecidableEq (DetectorIndex S) := Classical.decEq _

/-- The chosen finite-string detectors evaluate on the chosen literal string
modules as a Kronecker delta: dimension one on the matching inversion class
and zero on every other class. -/
theorem finrank_detectorSpace_rightModule_endpointWord
    (i j : DetectorIndex S) :
    Module.finrank k
        (EndpointWord.DetectorSpace
          (j.endpointWord.word.rightModule P.monomial) i.endpointWord) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact i.endpointWord.finrank_detectorSpace_rightModule_self
  · rw [if_neg hij]
    apply i.endpointWord.finrank_detectorSpace_rightModule_eq_zero_of_not_inverseEquivalent
    intro hinverse
    apply hij
    have hindex :=
      (ofWord_eq_iff S i.endpointWord.word j.endpointWord.word).2 hinverse
    simpa using hindex

end DetectorIndex

end MagnitudeConjecture.BoundQuiver.StringWord
