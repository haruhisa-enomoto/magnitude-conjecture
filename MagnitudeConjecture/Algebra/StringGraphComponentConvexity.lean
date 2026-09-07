import MagnitudeConjecture.Algebra.StringGraphComponentInterval

/-!
# Convex source support of string coefficient components

The forward partial-bijection relation linearly orders each generated
coefficient component.  Every source-word index between two component
vertices is therefore represented by a unique component vertex.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- Two vertices in one coefficient component are comparable by forward
reachability. -/
theorem reflTransGen_morphismCoefficientForwardStep_or_reverse_of_eqvGen
    (C D : Word R) {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.EqvGen (C.MorphismCoefficientStep D) p q) :
    Relation.ReflTransGen (C.MorphismCoefficientForwardStep D) p q ∨
      Relation.ReflTransGen (C.MorphismCoefficientForwardStep D) q p := by
  obtain ⟨r, hpr, hqr⟩ :=
    C.exists_common_morphismCoefficientForwardStep_of_eqvGen D hpq
  let forward := C.MorphismCoefficientForwardStep D
  have hrp : Relation.ReflTransGen (Function.swap forward) r p :=
    Relation.reflTransGen_swap.mpr hpr
  have hrq : Relation.ReflTransGen (Function.swap forward) r q :=
    Relation.reflTransGen_swap.mpr hqr
  have hreverseRightUnique : Relator.RightUnique (Function.swap forward) :=
    (C.morphismCoefficientForwardStep_leftUnique D).flip
  rcases Relation.ReflTransGen.total_of_right_unique
      hreverseRightUnique hrp hrq with hpq' | hqp'
  · exact Or.inr (Relation.reflTransGen_swap.mp hpq')
  · exact Or.inl (Relation.reflTransGen_swap.mp hqp')

/-- Component comparability is oriented by the order of source indices. -/
theorem reflTransGen_morphismCoefficientForwardStep_of_eqvGen_of_inputIndex_le
    (C D : Word R) {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.EqvGen (C.MorphismCoefficientStep D) p q)
    (hindex : p.inputIndex ≤ q.inputIndex) :
    Relation.ReflTransGen (C.MorphismCoefficientForwardStep D) p q := by
  rcases C.reflTransGen_morphismCoefficientForwardStep_or_reverse_of_eqvGen
      D hpq with hpq' | hqp
  · exact hpq'
  · have hreverseIndex :=
      C.inputIndex_le_of_reflTransGen_morphismCoefficientForwardStep D hqp
    have heq : p.inputIndex = q.inputIndex := Nat.le_antisymm hindex hreverseIndex
    have hpqEq := C.eq_of_morphismCoefficientStep_eqvGen_of_inputIndex_eq
      D hpq heq
    subst q
    exact Relation.ReflTransGen.refl

/-- Every integer index between the endpoints of a forward coefficient walk
occurs along that walk. -/
theorem exists_reflTransGen_morphismCoefficientForwardStep_inputIndex_eq
    (C D : Word R) {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.ReflTransGen
      (C.MorphismCoefficientForwardStep D) p q)
    (n : ℕ) (hpn : p.inputIndex ≤ n) (hnq : n ≤ q.inputIndex) :
    ∃ r, Relation.ReflTransGen
        (C.MorphismCoefficientForwardStep D) p r ∧
      r.inputIndex = n := by
  induction hpq with
  | refl =>
      have hn : p.inputIndex = n := Nat.le_antisymm hpn hnq
      exact ⟨p, Relation.ReflTransGen.refl, hn⟩
  | @tail q r hpq hqr ih =>
      by_cases hnr : n = r.inputIndex
      · exact ⟨r, hpq.tail hqr, hnr.symm⟩
      · have hsucc := hqr.2
        have hnq : n ≤ q.inputIndex := by omega
        exact ih hnq

/-- A forward walk whose input indices differ by exactly one is a single
forward edge. -/
theorem morphismCoefficientForwardStep_of_reflTransGen_of_inputIndex_add_one
    (C D : Word R) {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.ReflTransGen
      (C.MorphismCoefficientForwardStep D) p q)
    (hindex : q.inputIndex = p.inputIndex + 1) :
    C.MorphismCoefficientForwardStep D p q := by
  rcases hpq.cases_tail with h | ⟨r, hpr, hrq⟩
  · subst q
    omega
  · have hprIndex :=
      C.inputIndex_le_of_reflTransGen_morphismCoefficientForwardStep D hpr
    have hrqIndex := hrq.2
    have hindexEq : p.inputIndex = r.inputIndex := by omega
    have hprEq :=
      C.eq_of_reflTransGen_morphismCoefficientForwardStep_of_inputIndex_eq
        D hpr hindexEq
    subst r
    exact hrq

/-- A forward coefficient walk is contained in the original matched-step
component. -/
theorem morphismCoefficientStep_eqvGen_of_reflTransGen_forward
    (C D : Word R) {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.ReflTransGen
      (C.MorphismCoefficientForwardStep D) p q) :
    Relation.EqvGen (C.MorphismCoefficientStep D) p q := by
  induction hpq with
  | refl => exact Relation.EqvGen.refl _
  | tail hpr hrq ih =>
      apply Relation.EqvGen.trans _ _ _ ih
      rcases hrq.1 with hrq | hrq
      · exact Relation.EqvGen.rel _ _ hrq
      · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hrq)

/-- The source-index projection of a coefficient component is a convex
interval: every index between two supported indices is supported. -/
theorem exists_morphismCoefficientComponentSupport_inputIndex_eq_of_between
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    (p q : C.MorphismCoefficientComponentSupport D root)
    (n : ℕ) (hpn : p.1.inputIndex ≤ n) (hnq : n ≤ q.1.inputIndex) :
    ∃ r : C.MorphismCoefficientComponentSupport D root,
      r.1.inputIndex = n := by
  have hpq : Relation.EqvGen (C.MorphismCoefficientStep D) p.1 q.1 :=
    Relation.EqvGen.trans _ root _
      (Relation.EqvGen.symm _ _ p.2) q.2
  have hpqForward :=
    C.reflTransGen_morphismCoefficientForwardStep_of_eqvGen_of_inputIndex_le
      D hpq (hpn.trans hnq)
  obtain ⟨r, hpr, hrIndex⟩ :=
    C.exists_reflTransGen_morphismCoefficientForwardStep_inputIndex_eq
      D hpqForward n hpn hnq
  refine ⟨⟨r, ?_⟩, hrIndex⟩
  exact Relation.EqvGen.trans _ p.1 _ p.2
    (C.morphismCoefficientStep_eqvGen_of_reflTransGen_forward D hpr)

/-- Transposition identifies a component support with the corresponding
component support for the reversed word pair. -/
def morphismCoefficientComponentSupportTranspose
    (C D : Word R) (root : C.MorphismCoefficientPosition D) :
    C.MorphismCoefficientComponentSupport D root ≃
      D.MorphismCoefficientComponentSupport C
        (C.morphismCoefficientPositionTranspose D root) where
  toFun p := ⟨C.morphismCoefficientPositionTranspose D p.1,
    C.morphismCoefficientStep_eqvGen_transpose D p.2⟩
  invFun q := ⟨D.morphismCoefficientPositionTranspose C q.1, by
    simpa using
      D.morphismCoefficientStep_eqvGen_transpose C q.2⟩
  left_inv := by
    intro p
    apply Subtype.ext
    rcases p with ⟨⟨x, i, j⟩, hp⟩
    rfl
  right_inv := by
    intro q
    apply Subtype.ext
    rcases q with ⟨⟨x, j, i⟩, hq⟩
    rfl

@[simp]
theorem morphismCoefficientComponentSupportTranspose_apply_val
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    (p : C.MorphismCoefficientComponentSupport D root) :
    (C.morphismCoefficientComponentSupportTranspose D root p).1 =
      C.morphismCoefficientPositionTranspose D p.1 :=
  rfl

@[simp]
theorem morphismCoefficientComponentSupportTranspose_symm_apply_val
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    (q : D.MorphismCoefficientComponentSupport C
      (C.morphismCoefficientPositionTranspose D root)) :
    ((C.morphismCoefficientComponentSupportTranspose D root).symm q).1 =
      D.morphismCoefficientPositionTranspose C q.1 :=
  rfl

/-- The target-index projection of a coefficient component is also a convex
interval. -/
theorem exists_morphismCoefficientComponentSupport_outputIndex_eq_of_between
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    (p q : C.MorphismCoefficientComponentSupport D root)
    (n : ℕ) (hpn : p.1.outputIndex ≤ n) (hnq : n ≤ q.1.outputIndex) :
    ∃ r : C.MorphismCoefficientComponentSupport D root,
      r.1.outputIndex = n := by
  let e := C.morphismCoefficientComponentSupportTranspose D root
  obtain ⟨r, hr⟩ :=
    D.exists_morphismCoefficientComponentSupport_inputIndex_eq_of_between
      C (C.morphismCoefficientPositionTranspose D root)
      (e p) (e q) n (by simpa [e] using hpn) (by simpa [e] using hnq)
  refine ⟨e.symm r, ?_⟩
  simpa [e] using hr

/-- A forward coefficient edge changes the target-word index by one in one
of the two directions. -/
theorem MorphismCoefficientForwardStep.outputIndex (C D : Word R)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : C.MorphismCoefficientForwardStep D p q) :
    q.outputIndex = p.outputIndex + 1 ∨
      p.outputIndex = q.outputIndex + 1 := by
  rcases hpq.1 with hpq | hpq
  · exact (MorphismCoefficientStep.index C D hpq).2
  · rcases (MorphismCoefficientStep.index C D hpq).2 with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- The target direction cannot turn across two consecutive forward edges.
Such a turn would repeat a target position inside one component. -/
theorem morphismCoefficientForwardStep_outputIndex_no_turn
    (C D : Word R) {p q r : C.MorphismCoefficientPosition D}
    (hpq : C.MorphismCoefficientForwardStep D p q)
    (hqr : C.MorphismCoefficientForwardStep D q r) :
    (q.outputIndex = p.outputIndex + 1 ∧
        r.outputIndex = q.outputIndex + 1) ∨
      (p.outputIndex = q.outputIndex + 1 ∧
        q.outputIndex = r.outputIndex + 1) := by
  rcases hpq.outputIndex C D with hpqOut | hpqOut <;>
    rcases hqr.outputIndex C D with hqrOut | hqrOut
  · exact Or.inl ⟨hpqOut, hqrOut⟩
  · have hprOut : p.outputIndex = r.outputIndex := by omega
    have hprEqv : Relation.EqvGen (C.MorphismCoefficientStep D) p r :=
      Relation.EqvGen.trans _ q _
        (C.morphismCoefficientStep_eqvGen_of_reflTransGen_forward D
          (Relation.ReflTransGen.single hpq))
        (C.morphismCoefficientStep_eqvGen_of_reflTransGen_forward D
          (Relation.ReflTransGen.single hqr))
    have hpr := C.eq_of_morphismCoefficientStep_eqvGen_of_outputIndex_eq
      D hprEqv hprOut
    have hpqInput := hpq.2
    have hqrInput := hqr.2
    exfalso
    subst r
    omega
  · have hprOut : p.outputIndex = r.outputIndex := by omega
    have hprEqv : Relation.EqvGen (C.MorphismCoefficientStep D) p r :=
      Relation.EqvGen.trans _ q _
        (C.morphismCoefficientStep_eqvGen_of_reflTransGen_forward D
          (Relation.ReflTransGen.single hpq))
        (C.morphismCoefficientStep_eqvGen_of_reflTransGen_forward D
          (Relation.ReflTransGen.single hqr))
    have hpr := C.eq_of_morphismCoefficientStep_eqvGen_of_outputIndex_eq
      D hprEqv hprOut
    have hpqInput := hpq.2
    have hqrInput := hqr.2
    exfalso
    subst r
    omega
  · exact Or.inr ⟨hpqOut, hqrOut⟩

/-- Along a nonempty forward chain, the target index has one constant slope;
the final edge records the same slope as the endpoint formula. -/
theorem transGen_morphismCoefficientForwardStep_outputSlope_and_last
    (C D : Word R) {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.TransGen (C.MorphismCoefficientForwardStep D) p q) :
    (q.outputIndex = p.outputIndex + (q.inputIndex - p.inputIndex) ∧
        ∃ r, C.MorphismCoefficientForwardStep D r q ∧
          q.outputIndex = r.outputIndex + 1) ∨
      (p.outputIndex = q.outputIndex + (q.inputIndex - p.inputIndex) ∧
        ∃ r, C.MorphismCoefficientForwardStep D r q ∧
          r.outputIndex = q.outputIndex + 1) := by
  induction hpq with
  | single hpq =>
      rcases hpq.outputIndex C D with hout | hout
      · left
        refine ⟨?_, p, hpq, hout⟩
        have hin := hpq.2
        omega
      · right
        refine ⟨?_, p, hpq, hout⟩
        have hin := hpq.2
        omega
  | @tail q r hpq hqr ih =>
      have hpqInput :=
        C.inputIndex_le_of_reflTransGen_morphismCoefficientForwardStep D
          hpq.to_reflTransGen
      rcases ih with ⟨hpqOut, s, hsq, hsqOut⟩ |
          ⟨hpqOut, s, hsq, hsqOut⟩
      · rcases C.morphismCoefficientForwardStep_outputIndex_no_turn
          D hsq hqr with hsame | hopposite
        · left
          refine ⟨?_, q, hqr, hsame.2⟩
          have hin := hqr.2
          omega
        · exfalso
          omega
      · rcases C.morphismCoefficientForwardStep_outputIndex_no_turn
          D hsq hqr with hopposite | hsame
        · exfalso
          omega
        · right
          refine ⟨?_, q, hqr, hsame.2⟩
          have hin := hqr.2
          omega

/-- Endpoints of a nonempty forward chain have target displacement equal in
absolute value to their source displacement. -/
theorem transGen_morphismCoefficientForwardStep_outputSlope
    (C D : Word R) {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.TransGen (C.MorphismCoefficientForwardStep D) p q) :
    q.outputIndex = p.outputIndex + (q.inputIndex - p.inputIndex) ∨
      p.outputIndex = q.outputIndex + (q.inputIndex - p.inputIndex) := by
  rcases C.transGen_morphismCoefficientForwardStep_outputSlope_and_last
      D hpq with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- The same constant-slope formula, including the reflexive chain. -/
theorem reflTransGen_morphismCoefficientForwardStep_outputSlope
    (C D : Word R) {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.ReflTransGen (C.MorphismCoefficientForwardStep D) p q) :
    q.outputIndex = p.outputIndex + (q.inputIndex - p.inputIndex) ∨
      p.outputIndex = q.outputIndex + (q.inputIndex - p.inputIndex) := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hpq with h | h
  · subst q
    exact Or.inl (by simp)
  · exact C.transGen_morphismCoefficientForwardStep_outputSlope D h

/-- Within one coefficient component, ordering by source index identifies
the component correspondence with an interval map of constant slope one or
minus one. -/
theorem morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
    (C D : Word R) {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.EqvGen (C.MorphismCoefficientStep D) p q)
    (hindex : p.inputIndex ≤ q.inputIndex) :
    q.outputIndex = p.outputIndex + (q.inputIndex - p.inputIndex) ∨
      p.outputIndex = q.outputIndex + (q.inputIndex - p.inputIndex) := by
  exact C.reflTransGen_morphismCoefficientForwardStep_outputSlope D
    (C.reflTransGen_morphismCoefficientForwardStep_of_eqvGen_of_inputIndex_le
      D hpq hindex)

end MagnitudeConjecture.BoundQuiver.StringWord.Word
